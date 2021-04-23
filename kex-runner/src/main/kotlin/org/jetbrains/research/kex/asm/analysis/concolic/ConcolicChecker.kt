package org.jetbrains.research.kex.asm.analysis.concolic

import com.abdullin.kthelper.collection.firstOrElse
import com.abdullin.kthelper.collection.stackOf
import com.abdullin.kthelper.logging.log
import com.abdullin.kthelper.tryOrNull
import kotlinx.coroutines.TimeoutCancellationException
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeout
import kotlinx.coroutines.yield
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.random.Randomizer
import org.jetbrains.research.kex.smt.Checker
import org.jetbrains.research.kex.smt.Result
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.predicate.inverse
import org.jetbrains.research.kex.state.transformer.generateInputByModel
import org.jetbrains.research.kex.statistics.Statistics
import org.jetbrains.research.kex.trace.TraceManager
import org.jetbrains.research.kex.trace.`object`.*
import org.jetbrains.research.kex.trace.runner.ObjectTracingRunner
import org.jetbrains.research.kex.trace.runner.RandomObjectTracingRunner
import org.jetbrains.research.kex.trace.runner.TimeoutException
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.Value
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import org.jetbrains.research.kfg.ir.value.instruction.Instruction
import org.jetbrains.research.kfg.visitor.MethodVisitor
import java.time.Duration
import java.time.temporal.ChronoUnit
import java.util.*
import kotlin.NoSuchElementException
import kotlin.system.exitProcess


//Added CGS by AndreyBychkov https://github.com/AndreyBychkov

private val timeLimit by lazy { kexConfig.getLongValue("concolic", "timeLimit", 10000L) }
private val onlyMain by lazy { kexConfig.getBooleanValue("concolic", "main-only", false) }

class ConcolicChecker(val ctx: ExecutionContext, val manager: TraceManager<Trace>) : MethodVisitor {
    override val cm: ClassManager get() = ctx.cm
    val loader: ClassLoader get() = ctx.loader
    val random: Randomizer get() = ctx.random
    val paths = mutableSetOf<PredicateState>()


    override fun cleanup() {
        paths.clear()
    }

/*
    private fun analyze(method: Method) {
        log.debug(method.print())
        try {
            runBlocking {
                withTimeout(timeLimit) {
                    try {
                        val statistics = Statistics("CGS", method.toString(), 0, Duration.ZERO, 0)
                        processTree(method, statistics)
                        statistics.stopTimeMeasurement()
                        log.info(statistics.print())
                    } catch (e: TimeoutException) {
                        log.debug("Timeout on running $method")
                    }
                }
            }
        } catch (e: TimeoutCancellationException) {
            return
        }
    }

 */


    private fun analyze(method: Method) {
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
    }

    override fun visit(method: Method) {
        if (method.isStaticInitializer || method.isAbstract) return

        if ((onlyMain && method.name == "main") || !onlyMain) {
            analyze(method)
            print("")
        }
    }

    private fun buildState(method: Method, trace: Trace): PredicateState {
        data class BlockWrapper(val block: BasicBlock?)
        data class CallParams(val method: Method, val receiver: Value?, val instance: Value?, val args: Array<Value>)

        fun BasicBlock.wrap() = BlockWrapper(this)

        val methodStack = stackOf<Method>()
        val prevBlockStack = stackOf<BlockWrapper>()
        val filteredTrace = trace.actions.dropWhile { !(it is MethodEntry && it.method == method) }.run {
            var inStatic = false
            filter {
                when (it) {
                    is StaticInitEntry -> {
                        inStatic = true
                        false
                    }
                    is StaticInitExit -> {
                        inStatic = false
                        false
                    }
                    else -> !inStatic
                }
            }
        }

        val builder = ConcolicStateBuilder(cm)
        var methodParams: CallParams? = null
        for ((index, action) in filteredTrace.withIndex()) {
            when (action) {
                is MethodEntry -> {
                    methodStack.push(action.method)
                    prevBlockStack.push(BlockWrapper(null))
                    if (methodParams != null && methodParams.method == action.method) {
                        val mappings = mutableMapOf<Value, Value>()
                        methodParams.instance?.run { mappings[values.getThis(action.method.`class`)] = this }
                        methodParams.args.withIndex().forEach { (index, arg) ->
                            mappings[values.getArgument(index, action.method, action.method.argTypes[index])] = arg
                        }
                        builder.enterMethod(action.method, ConcolicStateBuilder.CallParameters(methodParams.receiver, mappings))
                    } else {
                        builder.enterMethod(action.method)
                    }
                    methodParams = null
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
                    methodParams = CallParams(action.method, action.returnValue, action.instance, action.args)
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

    private fun collectTrace(method: Method, instance: Any?, args: Array<Any?>): Trace {
        val runner = ObjectTracingRunner(method, loader)
        return runner.collectTrace(instance, args)
    }

    private fun getRandomTrace(method: Method) = RandomObjectTracingRunner(method, loader, ctx.random).run()

    private suspend fun process(method: Method, statistics: Statistics) {
        val traces = ArrayDeque<Trace>()
        while (!manager.isBodyCovered(method)) {
            val candidate = traces.firstOrElse {
                statistics.iterations += 1
                getRandomTrace(method)?.also { manager[method] = it }
            } ?: return
            yield()

            statistics.iterations += 1
            run(method, candidate)?.also {
                manager[method] = it
                traces.add(it)
                statistics.satNum += 1
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

    suspend fun getRandomTraceUntilSuccess(method: Method): Trace {
        var trace: Trace? = null
        while (trace == null || trace.actions.isEmpty()) {
            trace = getRandomTrace(method)?.also { manager[method] = it }
            yield()
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

        val psa = PredicateStateAnalysis(cm)
        val checker = Checker(method, loader, psa)
        val result = checker.prepareAndCheck(mutated)
        if (result !is Result.SatResult) return null
        yield()

        val (instance, args) = tryOrNull {
            generateInputByModel(ctx, method, checker.state, result.model)
        } ?: return null
        yield()

        val resultingTrace = tryOrNull { collectTrace(method, instance, args) } ?: return null
        if (buildState(method, resultingTrace).path.startsWith(path))
            paths += path
        return resultingTrace
    }

    private suspend fun processCFGDS(method: Method) {
        val graph = StaticGraph(method)
        cfgds(graph)
    }

    private fun getState(block: BasicBlock): PredicateState? {
        val psa = PredicateStateAnalysis(cm)
        val builder = psa.builder(block.parent)
        return builder.getInstructionState(block.terminator)
    }

    //contains no problems
    private suspend fun execute(method: Method, trace: Trace, ps: PredicateState): Trace? {
        //val state = buildState(method, trace)
        //state += ps?
        val path = ps.path //mutated.path
        if (path in paths) {
            log.debug("Could not generate new trace")
            return null
        }
        //log.debug("Collected trace: $state")
        log.debug("New trace: $ps")

        val psa = PredicateStateAnalysis(cm)
        val checker = Checker(method, loader, psa)
        val result = checker.prepareAndCheck(ps)
        if (result !is Result.SatResult) return null
        yield()

        val (instance, args) = tryOrNull {
            generateInputByModel(ctx, method, checker.state, result.model)
        } ?: return null
        yield()

        val resultingTrace = tryOrNull { collectTrace(method, instance, args) } ?: return null
        if (buildState(method, resultingTrace).path.startsWith(path))
            paths += path
        return resultingTrace
    }


    private fun traceToSetVertex(graph: StaticGraph, trace: Trace): MutableSet<Vertex> {
        fun Instruction.find() = graph.vertices.find {it.inst == this}

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
                        val vert = temp.find { it.method == action.method }?.find()?: continue
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
                    val vert = currentBlock.instructions.first().find()?: continue
                    set.add(vert)
                    continue
                }
                is BlockJump -> {
                    currentBlock = action.block
                    val vert = currentBlock.terminator.find()?: continue
                    set.add(vert)
                    continue
                }
                is BlockBranch -> {
                    currentBlock = action.block
                    val vert = currentBlock.terminator.find()?: continue
                    set.add(vert)
                }
                is BlockSwitch -> {
                    currentBlock = action.block
                    val vert = currentBlock.terminator.find()?: continue
                    set.add(vert)
                }
            }
        }
        return set
    }

    private suspend fun searchAlongPath(graph: StaticGraph, trace: Trace, path: MutableMap<Vertex, Vertex>,
                                        failed: MutableSet<Vertex>, ud: Int): Trace? {
        //1)path.foreach(trace.actions.contains(it)) -> find mismatch as path[i]
        //2)if we didnt found mismatch return lastTrace
        //3)else force prev as path[i-1] -> tempTrace
        //  4)if forcing succeed lastTrace = tempTrace
        //  5)else
        //fun Instruction.find() = graph.vertices.find {it.inst == this}
        var lastTrace = trace

        while(true){
            var mismatch: Vertex? = null

            val set = traceToSetVertex(graph, lastTrace)
            var numberMatched = 0
            for(vert in path.values) {
                if(set.contains(vert)) {
                    numberMatched++
                    continue
                }
                else {
                    mismatch = vert
                    break
                }
            }

            if(mismatch == null)
                return if(numberMatched>0)
                    lastTrace
                else null

            //val ps = getState(mismatch.bb)  //???? should we force mismatch.predecessor.bb instead?
            val ps = getState(mismatch.inst.parent)
            mismatch.tries++

            if(ps == null || ps.isEmpty) {
                log.debug("SAP: could not generate a predicateState")
                failed.add(mismatch)       //same as above
                return if(numberMatched>0)
                    lastTrace
                else null
            }

            val tempTrace = execute(graph.rootMethod, lastTrace, ps)
            yield()
            if(tempTrace == null || tempTrace.actions.isNullOrEmpty())  {
                log.debug("SAP: could not process a trace...")
                failed.add(mismatch)       //same as above
                return if(numberMatched>0)
                    lastTrace
                else null
            }

            lastTrace = tempTrace
            graph.addTrace(lastTrace)

            log.debug("SAP: an iteration of sap worked correctly")
            continue
        }

    }

    //the search terminates in failure
    //if it runs out of branches to select, it exhausts its budget of
    //test iterations, or if it uncovers no new branches after some
    //set number of iterations.


    private suspend fun finish(graph: StaticGraph) {
        log.debug("Finishing the search")

        val count = graph.vertices.size.toDouble()
        var covered = 0.0

        for(vertex in graph.vertices) {
            if(vertex.isCovered)
                covered += 1.0
        }

        var graphCoverage: Double = (covered/count).toDouble() * 100
        log.debug("========================================================")
        log.debug("Total static graph coverage is $graphCoverage %")
        //log.debug(graph.vertices.toString())
        log.debug("========================================================")
        yield()
        //exitProcess(0)

        //something about finishing our search and printing stats or smth like that
        //do we need this?
    }

    suspend fun cfgds(graph: StaticGraph) {

        var lastTrace = getRandomTraceUntilSuccess(graph.rootMethod)
        yield()
        graph.addTrace(lastTrace)


        val failedToForce = mutableSetOf<Vertex>()
        var failedIterations = 0

        while (true) {

            if(failedIterations > 20) {
                log.debug("CFGDS: too many failed iterations in a row, exiting")
                break
            }

            log.debug("another iteration of CFGDS")

            //graph.dropTries()

            log.debug("CFGDS: Searching for a branch to force...")
            val found = graph.nextBranchToForce(failedToForce)

            if (found == null) {
                failedIterations++
                log.debug("====================Could not find a branch to force")
                continue
                //break
            }



            log.debug("found a branch")


            //here we should have checked if there were any covered branches
            // and finish our search in case there weren't
            // after some set number of iterations

            //val branch = found.bb
            val branch = found.inst.parent

            val ps = getState(branch)
            found.tries++

            if (ps == null || ps.isEmpty) {
                log.debug("Could not generate a PredicateState for block $branch")
                failedIterations++
                failedToForce.add(found)
                continue
            }

            val tempTrace = execute(graph.rootMethod, lastTrace, ps)
            yield()
            log.debug("just generated a trace")

            if(tempTrace == null || tempTrace.actions.isNullOrEmpty()) {
                log.debug("Could not process a trace for branch $branch")
                failedIterations++
                failedToForce.add(found)
                continue
            }
            lastTrace = tempTrace

            val newBranchCovered = graph.addTrace(lastTrace)

            if(!newBranchCovered) {
                failedIterations++
                failedToForce.add(found)
                log.debug("CFGDS: Processing a trace was successful, but no new branches are covered")
            }
            else {
                failedIterations = 0
            }
            if(failedIterations > 20) {
                log.debug("CFGDS: too many failed iterations in a row, exiting")
                break
            }

            val ud = found.uncoveredDistance + found.tries
            log.debug("entering searchAlongPath")

            val pathList = graph.findPathsForSAP(found, ud)
            yield()

            if(pathList.isEmpty()) {
                log.debug("No path found for SAP, continuing")
                found.tries+=1
                continue
            }

            var sapSucceed = false

            for(path in pathList) {
                val trace = searchAlongPath(graph, lastTrace, path, failedToForce, ud)
                yield()
                if(trace==null || trace.actions.isNullOrEmpty()) {
                    log.debug("SAP: did not succeed on current iteration")
                    continue
                }
                sapSucceed = true
                lastTrace = trace
                break
            }

            if(!sapSucceed){
                found.tries++
                continue
            }
            else {
                graph.addTrace(lastTrace)
                graph.dropTries()
            }
            log.debug("SearchAlongPath finished, trying to force a new branch in CFGDS")
        }
        finish(graph)
    }


}