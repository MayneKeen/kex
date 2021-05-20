package org.jetbrains.research.kex.asm.analysis.concolic

import org.jetbrains.research.kthelper.collection.firstOrElse
import org.jetbrains.research.kthelper.collection.stackOf
import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kthelper.tryOrNull
import kotlinx.coroutines.TimeoutCancellationException
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeout
import kotlinx.coroutines.yield
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.random.Randomizer
import org.jetbrains.research.kex.reanimator.ParameterGenerator
import org.jetbrains.research.kex.reanimator.Reanimator
import org.jetbrains.research.kex.smt.Checker
import org.jetbrains.research.kex.smt.Result
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.predicate.inverse
//import org.jetbrains.research.kex.state.transformer.generateInputByModel
import org.jetbrains.research.kex.statistics.Statistics
import org.jetbrains.research.kex.trace.TraceManager
import org.jetbrains.research.kex.trace.`object`.*
import org.jetbrains.research.kex.trace.runner.ObjectTracingRunner
import org.jetbrains.research.kex.trace.runner.RandomObjectTracingRunner
import org.jetbrains.research.kex.trace.runner.TimeoutException
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.Value
import org.jetbrains.research.kfg.ir.value.instruction.*
import org.jetbrains.research.kfg.visitor.MethodVisitor
import java.util.*

private val timeLimit by lazy { kexConfig.getLongValue("concolic", "timeLimit", 10000L) }
private val onlyMain by lazy { kexConfig.getBooleanValue("concolic", "main-only", false) }

class ConcolicChecker(
    val ctx: ExecutionContext,
    val psa: PredicateStateAnalysis,
    private val manager: TraceManager<Trace>,
    val target: Package
) : MethodVisitor {
    override val cm: ClassManager get() = ctx.cm
    val loader: ClassLoader get() = ctx.loader
    val random: Randomizer get() = ctx.random
    private val paths = mutableSetOf<PredicateState>()
    private var counter = 0
    lateinit var generator: ParameterGenerator
        protected set

    override fun cleanup() {
        paths.clear()
    }

    private fun initializeGenerator(method: Method) {
        generator = Reanimator(ctx, psa, method)
    }

    private fun analyze(method: Method, target: Package) {
        log.debug(method.print())
        initializeGenerator(method)
        try {
            runBlocking {
                withTimeout(timeLimit) {
                    try {
                        //process(method)
                        processCFGDS(method, target)
                    } catch (e: TimeoutException) {
                        log.debug("Timeout on running $method")
                    }
                }
            }
        } catch (e: TimeoutCancellationException) {
            log.debug("Processing of method $method is stopped due timeout")
        }
        generator.emit()
    }


    /*
    * private fun analyze(method: Method) {
        log.debug(method.print())
        try {
            runBlocking {
                withTimeout(timeLimit) {
                    try {
                        //val statistics = Statistics("CGS", method.toString(), 0, Duration.ZERO, 0)
                        //processTree(method, statistics)
                        processCFGDS(method)
                        //statistics.stopTimeMeasurement()
                        //log.info(statistics.print())
                    } catch (e: TimeoutException) {
                        log.debug("Timeout on running $method")
                    }
                }
            }
        } catch (e: TimeoutCancellationException) {
            return
        }
    }*/


    override fun visit(method: Method) {
        if (method.isStaticInitializer || method.isAbstract) return

        if ((onlyMain && method.name == "main") || !onlyMain) {
            analyze(method, target)
        }
    }

    private fun buildState(method: Method, trace: Trace): PredicateState {
        data class BlockWrapper(val block: BasicBlock?)

        fun BasicBlock.wrap() = BlockWrapper(this)

        val methodStack = stackOf<Method>()
        val prevBlockStack = stackOf<BlockWrapper>()
        val filteredTrace = trace.actions.run {
            var staticLevel = 0
            filter {
                when (it) {
                    is StaticInitEntry -> {
                        ++staticLevel
                        false
                    }
                    is StaticInitExit -> {
                        --staticLevel
                        false
                    }
                    else -> staticLevel == 0
                }
            }
        }.dropWhile { !(it is MethodEntry && it.method == method) }

        val builder = ConcolicStateBuilder(cm, psa)
        for ((index, action) in filteredTrace.withIndex()) {
            when (action) {
                is MethodEntry -> {
                    methodStack.push(action.method)
                    prevBlockStack.push(BlockWrapper(null))
                    builder.enterMethod(action.method)
                }
                is MethodReturn -> {
                    val prevBlock = prevBlockStack.pop()
                    val current = action.block
                    val next = filteredTrace.getOrNull(index + 1) as? BlockAction
                    builder.build(current, prevBlock.block, next?.block)
                    methodStack.pop()
                    builder.exitMethod(action.method)
                }
                is MethodThrow -> {
                    val prevBlock = prevBlockStack.pop()
                    val current = action.block
                    val next = filteredTrace.getOrNull(index + 1) as? BlockAction
                    builder.build(current, prevBlock.block, next?.block)
                    methodStack.pop()
                    builder.exitMethod(action.method)
                }
                is MethodCall -> {
                    val mappings = mutableMapOf<Value, Value>()
                    action.instance?.run { mappings[values.getThis(action.method.`class`)] = this }
                    action.args.withIndex().forEach { (index, arg) ->
                        mappings[values.getArgument(index, action.method, action.method.argTypes[index])] = arg
                    }
                    builder.callMethod(action.method, ConcolicStateBuilder.CallParameters(action.returnValue, mappings))
                }
                is BlockJump -> {
                    val prevBlock = prevBlockStack.pop()
                    val current = action.block
                    val next = filteredTrace.getOrNull(index + 1) as? BlockAction
                    builder.build(current, prevBlock.block, next?.block)
                    prevBlockStack.push(current.wrap())
                }
                is BlockBranch -> {
                    val prevBlock = prevBlockStack.pop()
                    val current = action.block
                    val next = filteredTrace.getOrNull(index + 1) as? BlockAction
                    builder.build(current, prevBlock.block, next?.block)
                    prevBlockStack.push(current.wrap())
                }
                is BlockSwitch -> {
                    val prevBlock = prevBlockStack.pop()
                    val current = action.block
                    val next = filteredTrace.getOrNull(index + 1) as? BlockAction
                    builder.build(current, prevBlock.block, next?.block)
                    prevBlockStack.push(current.wrap())
                }
                else -> {
                }
            }
        }
        return builder.apply()
    }

    private fun mutate(ps: PredicateState): PredicateState {
        infix fun PredicateState.covered(set: Set<PredicateState>): Boolean {
            return set.any { it.startsWith(this) }
        }

        val currentPath = StateBuilder()
        val currentState = StateBuilder()
        ps.takeWhile {
            if (it.type != PredicateType.Path()) {
                currentState += it
                false
            } else {
                val current = it.inverse()
                when {
                    (currentPath + current).apply() covered paths -> {
                        currentPath += it
                        currentState += it
                        false
                    }
                    else -> {
                        currentState += current
                        true
                    }
                }
            }
        }
        return currentState.apply()
    }

    private fun collectTrace(method: Method, instance: Any?, args: List<Any?>): Trace {
        val runner = ObjectTracingRunner(method, loader)
        return runner.collectTrace(instance, args.toTypedArray())
    }

    private fun getRandomTrace(method: Method) =
        tryOrNull { RandomObjectTracingRunner(method, loader, ctx.random).run() }

    private suspend fun process(method: Method) {
        val traces = ArrayDeque<Trace>()
        while (!manager.isBodyCovered(method)) {
            val candidate = traces.firstOrElse { getRandomTrace(method)?.also { manager[method] = it } } ?: return
            yield()

            run(method, candidate)?.also {
                manager[method] = it
                traces.add(it)
            }
            yield()
        }
    }

    private suspend fun processTree(method: Method, statistics: Statistics) {
        var contextLevel = 1
        val contextCache = mutableSetOf<TraceGraph.Context>()
        val visitedBranches = mutableSetOf<TraceGraph.Branch>()

        val startTrace: Trace = getRandomTrace(method)?.also { manager[method] = it } ?: return
        if (startTrace.actions.isEmpty()) return
        val traces = DominatorTraceGraph(startTrace)

        while (!manager.isBodyCovered(method)) {
            statistics.iterations += 1
            var tb = traces.getTracesAndBranches().filter { it.second !in visitedBranches }
            while (tb.isEmpty()) {
                statistics.iterations += 1
                val randomTrace = getRandomTrace(method)?.also { manager[method] = it; } ?: return
                val randomBranch = TraceGraph.Branch(randomTrace.actions)
                tb = listOfNotNull(randomTrace to randomBranch).filter { it.second !in visitedBranches }
                yield()
            }

            tb.asSequence()
                .filter { (_, branch) -> branch.context(contextLevel) !in contextCache }
                .forEach { (candidate, branch) ->
                    statistics.iterations += 1
                    run(method, candidate)?.also {
                        manager[method] = it
                        traces.addTrace(it)
                        statistics.satNum += 1
                    }
                    manager[method] = candidate
                    contextCache.add(branch.context(contextLevel))
                    visitedBranches.add(traces.toBranch(candidate))
                    yield()
                }
            contextLevel += 1
            yield()
        }
    }


    private suspend fun getRandomTraceUntilSuccess(method: Method): Trace? {
        var trace: Trace? = null
        var iterations = 0
        while (iterations < 10 && (trace == null || trace.actions.isEmpty())) {
            trace = getRandomTrace(method)?.also { manager[method] = it }
            yield()
            iterations++
        }
        return trace
    }

    private suspend fun run(method: Method, trace: Trace): Trace? {
        val state = buildState(method, trace)
        val mutated = mutate(state)
        val path = mutated.path
        if (path in paths) {
            log.debug("Could not generate new trace")
            return null
        }
        log.debug("Collected trace: $state")
        log.debug("Mutated trace: $mutated")

        val checker = Checker(method, loader, psa)
        val result = checker.prepareAndCheck(mutated)
        if (result !is Result.SatResult) return null
        yield()

        val (instance, args) = tryOrNull {
            generator.generate("test${++counter}", method, checker.state, result.model)
        } ?: return null
        yield()

        val resultingTrace = tryOrNull { collectTrace(method, instance, args) } ?: return null
        if (buildState(method, resultingTrace).path.startsWith(path))
            paths += path
        return resultingTrace
    }

    private suspend fun processCFGDS(method: Method, target: Package) {
        if (!method.hasBody) {
            log.debug("Method $method is empty or has empty body")
            return
        }
        val graph = StaticGraph(method, target)
        cfgds(graph)
        yield()

        return
    }

    private fun getState(block: BasicBlock): PredicateState? {
        val psa = PredicateStateAnalysis(cm)
        val builder = psa.builder(block.parent)
        return builder.getInstructionState(block.terminator)
    }

    private fun getStateByInst(inst: Instruction) =
        PredicateStateAnalysis(cm).builder(inst.parent.parent).getInstructionState(inst)

    private suspend fun execute(method: Method, trace: Trace, ps: PredicateState): Trace? {
        val path = ps.path //mutated.path
        if (path in paths) {
            log.debug("Generated an already existing path")
            return null
        }
        log.debug("New trace: $ps")

        val psa = PredicateStateAnalysis(cm)
        val checker = Checker(method, loader, psa)
        val result = checker.prepareAndCheck(ps)
        if (result !is Result.SatResult) return null
        yield()

        val (instance, args) = tryOrNull {
            generator.generate("test${++counter}", method, checker.state, result.model)
            //generateInputByModel(ctx, method, checker.state, result.model)
        } ?: return null
        yield()

        val resultingTrace = tryOrNull { collectTrace(method, instance, args) } ?: return null
        if (buildState(method, resultingTrace).path.startsWith(path))
            paths += path
        return resultingTrace
    }

    private fun traceToSetVertex(graph: StaticGraph, trace: Trace): MutableSet<Vertex> {
        fun Instruction.find() = graph.vertices.find { it.inst == this }

        val set = mutableSetOf<Vertex>()

        for (action in trace.actions) {
            var currentBlock: BasicBlock? = null

            when (action) {
                is MethodEntry -> {
                    continue
                }               //??
                is MethodReturn -> {
                    continue
                }             //??
                is MethodThrow -> {
                    continue
                }              //??
                is MethodCall -> {
                    if (currentBlock != null && currentBlock.isNotEmpty) {
                        val temp = currentBlock.instructions.filterIsInstance<CallInst>()
                        val vert = temp.find { it.method == action.method }?.find() ?: continue
                        set.add(vert)
                        continue
                    }
                }
                is StaticInitEntry -> {
                    continue
                }
                is StaticInitExit -> {
                    continue
                }
                is BlockEntry -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.instructions.first().find() ?: continue
                    set.add(vert)
                    continue
                }
                is BlockJump -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.terminator.find() ?: continue
                    set.add(vert)
                    continue
                }
                is BlockBranch -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.terminator.find() ?: continue
                    set.add(vert)
                }
                is BlockSwitch -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.terminator.find() ?: continue
                    set.add(vert)
                }
            }
        }
        return set
    }

    private fun findMismatch(
        method: Method,
        graph: StaticGraph,
        trace: Trace,
        path: MutableList<Vertex>
    ): PredicateState? {
        data class BlockWrapper(val block: BasicBlock?)

        fun BasicBlock.wrap() = BlockWrapper(this)

        val methodStack = stackOf<Method>()
        val prevBlockStack = stackOf<BlockWrapper>()
        val filteredTrace = trace.actions.run {
            var staticLevel = 0
            filter {
                when (it) {
                    is StaticInitEntry -> {
                        ++staticLevel
                        false
                    }
                    is StaticInitExit -> {
                        --staticLevel
                        false
                    }
                    else -> staticLevel == 0
                }
            }
        }.dropWhile { !(it is MethodEntry && it.method == method) }

        fun Instruction.find() = graph.vertices.find { it.inst == this }
        var currentBlock: BasicBlock? = null
        val builder = ConcolicStateBuilder(cm, psa)
        var completelyMatched = true
        var prevVert = path.first()

        for ((index, action) in filteredTrace.withIndex()) {
            when (action) {
                is MethodEntry -> {
                    methodStack.push(action.method)
                    prevBlockStack.push(BlockWrapper(null))
                    builder.enterMethod(action.method)
                    continue
                }
                is MethodReturn -> {
                    val prevBlock = prevBlockStack.pop()
                    val current = action.block
                    val next = filteredTrace.getOrNull(index + 1) as? BlockAction
                    builder.build(current, prevBlock.block, next?.block)
                    methodStack.pop()
                    builder.exitMethod(action.method)
                    continue
                }
                is MethodThrow -> {
                    val prevBlock = prevBlockStack.pop()
                    val current = action.block
                    val next = filteredTrace.getOrNull(index + 1) as? BlockAction
                    builder.build(current, prevBlock.block, next?.block)
                    methodStack.pop()
                    builder.exitMethod(action.method)
                    continue
                }
                is MethodCall -> {
                    if (currentBlock == null || currentBlock.isEmpty) {
                        val mappings = mutableMapOf<Value, Value>()
                        action.instance?.run { mappings[values.getThis(action.method.`class`)] = this }
                        action.args.withIndex().forEach { (index, arg) ->
                            mappings[values.getArgument(index, action.method, action.method.argTypes[index])] = arg
                        }
                        builder.callMethod(
                            action.method,
                            ConcolicStateBuilder.CallParameters(action.returnValue, mappings)
                        )
                        continue
                    }

                    val callVerts = currentBlock.instructions.filterIsInstance<CallInst>()
                    val vert = callVerts.find { it.method == action.method }?.find()

                    if (vert == null || path.contains(vert)) {
                        val mappings = mutableMapOf<Value, Value>()
                        action.instance?.run { mappings[values.getThis(action.method.`class`)] = this }
                        action.args.withIndex().forEach { (index, arg) ->
                            mappings[values.getArgument(index, action.method, action.method.argTypes[index])] = arg
                        }
                        builder.callMethod(
                            action.method,
                            ConcolicStateBuilder.CallParameters(action.returnValue, mappings)
                        )
                        if (vert != null)
                            prevVert = vert
                        continue
                    }
                    completelyMatched = false
                    if (prevVert is TerminateVert) {
                        builder.forceByType(prevVert, currentBlock, path)
                        break
                    }

                }
                is BlockEntry -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.instructions.first().find()

                    if (vert == null || path.contains(vert)) {
                        continue
                    }
                    completelyMatched = false
                    if (prevVert is TerminateVert) {
                        builder.forceByType(prevVert, currentBlock, path)
                        break
                    }

                    continue
                }

                is BlockJump -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.terminator.find()
                    if (vert == null || path.contains(vert)) {
                        val prevBlock = prevBlockStack.pop()
                        val current = action.block
                        val next = filteredTrace.getOrNull(index + 1) as? BlockAction
                        builder.build(current, prevBlock.block, next?.block)
                        prevBlockStack.push(current.wrap())
                        continue
                    }
                    completelyMatched = false
                    if (prevVert is TerminateVert) {
                        builder.forceByType(prevVert, currentBlock, path)
                        break
                    }
                }
                is BlockBranch -> {

                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        log.debug("current block is empty")

                    val vert = currentBlock.terminator.find()!!

                    if (path.contains(vert)) {
                        prevVert = vert
                        val prevBlock = prevBlockStack.pop()
                        val current = action.block
                        val next = filteredTrace.getOrNull(index + 1) as? BlockAction
                        builder.build(current, prevBlock.block, next?.block)
                        prevBlockStack.push(current.wrap())
                        continue
                    }
                    completelyMatched = false
                    if (prevVert is TerminateVert) {
                        builder.forceByType(prevVert, currentBlock, path)
                        break
                    }

                }
                is BlockSwitch -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        log.debug("current block is empty")

                    val vert = currentBlock.terminator.find()!!

                    if (path.contains(vert)) {
                        prevVert = vert
                        val prevBlock = prevBlockStack.pop()
                        val current = action.block
                        val next = filteredTrace.getOrNull(index + 1) as? BlockAction
                        builder.build(current, prevBlock.block, next?.block)
                        prevBlockStack.push(current.wrap())
                        continue
                    }
                    completelyMatched = false
                    if (prevVert is TerminateVert) {
                        builder.forceByType(prevVert, currentBlock, path)
                        break
                    }
                }
                else -> {
                }
            }
        }
        return if (completelyMatched)
            null
        else
            builder.apply()
    }

    private fun getPaths(graph: StaticGraph, trace: Trace, vertex: Vertex, ud: Int): MutableList<MutableList<Vertex>> {
        val paths = graph.findPathsForSAP(vertex, ud)
        if(paths.isEmpty())
            return mutableListOf()
        val traceVertices = traceToSetVertex(graph, trace)
        if(!traceVertices.contains(vertex)) {
            log.debug("Graph: smth went wrong, vertex is not in trace")
            return mutableListOf()
        }
        val pathBeginning = mutableListOf<Vertex>()
        val result = mutableListOf<MutableList<Vertex>>()

        for(v in traceVertices)
            if(v == vertex)
                break
            else
                pathBeginning.add(v)

       for(path in paths) {
           val list = mutableListOf<Vertex>()
           list.addAll(pathBeginning)
           list.addAll(path)
           result.add(list)
       }
        return result
    }

    private suspend fun searchAlongPath(
        graph: StaticGraph, trace: Trace, path: MutableList<Vertex>,
        ): Trace? {
        //fun Instruction.find() = graph.vertices.find {it.inst == this}
        var lastTrace = trace
        var failedIterations = 0

        var bound = path.filter {
            it.inst is BranchInst || it.inst is SwitchInst || it.inst is TableSwitchInst
        }.size

        while (bound > 0) {
            val ps = findMismatch(graph.rootMethod, graph, trace, path)

            if (ps == null && lastTrace != trace) {
                log.debug("SAP: succeed")
                return lastTrace
            }

            if (ps == null || ps.isEmpty) {
                log.debug("SAP: could not generate a predicateState")
                //failed.add(mismatch)       //same as above
                return if (lastTrace != trace)
                    lastTrace
                else null
            }

            val tempTrace = execute(graph.rootMethod, lastTrace, ps)
            yield()
            bound--

            if (tempTrace == null || tempTrace.actions.isNullOrEmpty()) {
                log.debug("SAP: could not process a trace...")
                return if (lastTrace != trace)
                    lastTrace
                else null
            }

            lastTrace = tempTrace
            val newBranchCovered = graph.addTrace(lastTrace)

            if (!newBranchCovered) {
                log.debug("SAP: a failed iteration")
                failedIterations++
            }
            if (failedIterations > 20) {
                log.debug("SAP: did not succeed, too many failed iterations in a row")
                return lastTrace
            }

            log.debug("SAP: an iteration of sap finished correctly")
        }
        return lastTrace
    }

    //the search terminates in failure
    //if it runs out of branches to select, it exhausts its budget of
    //test iterations, or if it uncovers no new branches after some
    //set number of iterations.

    private suspend fun finish(graph: StaticGraph) {
        log.debug("Finishing the search")

        val count = graph.vertices.size.toDouble()
        var covered = 0.0

        for (vertex in graph.vertices) {
            if (vertex.isCovered)
                covered += 1.0
        }

        var graphCoverage = (covered / count) * 100
        log.debug("========================================================")
        log.debug("Total static graph coverage for ${graph.rootMethod} is $graphCoverage %")
        log.debug("========================================================")
        yield()
    }

    suspend fun cfgds(graph: StaticGraph) {

        var lastTrace = getRandomTraceUntilSuccess(graph.rootMethod)
        yield()

        if (lastTrace == null || lastTrace.actions.isEmpty()) {
            log.debug("CFGDS: Could not process any trace in method ${graph.rootMethod}")
            return
        }

        graph.addTrace(lastTrace)

        val failedToForce = mutableSetOf<Vertex>()
        var failedIterations = 0

        while (true) {

            if (failedIterations > 20) {
                log.debug("CFGDS: too many failed iterations in a row, exiting")
                break
            }

            log.debug("another iteration of CFGDS")
            //graph.dropTries()

            log.debug("CFGDS: Searching for a branch to force...")
            var found = graph.nextBranchToForce(failedToForce/*alreadyForced*/)

            val uncoveredBranches = graph.vertices.filter {
                (it.inst is BranchInst || it.inst is SwitchInst || it.inst is TableSwitchInst) && !it.isCovered
            }

            if (found == null && uncoveredBranches.isNotEmpty()) {
                found = uncoveredBranches.random()
            }

            if (found == null) {
                log.debug("CFGDS: Could not find a branch to force, exiting")
                break
            }

            log.debug("found a branch")
            val branch = found.inst.parent

            val ps = getState(branch)
            found.tries++

            if (ps == null || ps.isEmpty) {
                log.debug("CFGDS: Could not generate a PredicateState for block $branch")
                failedIterations++
                failedToForce.add(found)
                continue
            }

            val tempTrace = execute(graph.rootMethod, lastTrace!!, ps)
            yield()


            if (tempTrace == null || tempTrace.actions.isNullOrEmpty()) {
                log.debug("CFGDS: Could not process a trace for branch $branch")
                failedIterations++
                failedToForce.add(found)
                continue
            }
            lastTrace = tempTrace
            log.debug("CFGDS: Just generated a trace")
            val newBranchCovered = graph.addTrace(lastTrace)

            if (!newBranchCovered) {
                failedIterations++
                log.debug("CFGDS: Processing a trace was successful, but no new branches are covered")
            } else {
                failedIterations = 0
            }
            if (failedIterations > 20) {
                log.debug("CFGDS: too many failed iterations in a row, exiting")
                break
            }

            val ud =
                if (found.uncoveredDistance + found.tries > 0)
                    found.uncoveredDistance + found.tries
                else
                    Int.MAX_VALUE

            log.debug("CFGDS: entering searchAlongPath")

            val pathList = getPaths(graph, lastTrace, found, ud)
            yield()

            if (pathList.isEmpty()) {
                log.debug("CFGDS: No path found for SAP, continuing")
                found.tries += 1
                continue
            } else {
                log.debug("CFGDS: A path for SAP has been found")

            }
            var sapSucceed = false
            for (path in pathList) {
                val trace = searchAlongPath(graph, lastTrace!!, path)
                yield()
                if (trace == null || trace.actions.isNullOrEmpty()) {
                    log.debug("CFGDS: SAP did not succeed on current iteration")
                    continue
                }
                sapSucceed = true
                lastTrace = trace
                break
            }

            if (!sapSucceed) {
                found.tries++
                continue
            } else {
                graph.addTrace(lastTrace!!)
                graph.dropTries()
            }
            log.debug("CFGDS: SearchAlongPath finished, trying to force a new branch in CFGDS")
        }
        finish(graph)
    }
}
