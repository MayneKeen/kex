package org.jetbrains.research.kex.asm.analysis.concolic

import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.yield
import org.jetbrains.research.kthelper.collection.queueOf
import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.trace.`object`.*
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.*
import org.jetbrains.research.kfg.ir.value.instruction.*

class StaticGraph(enterPoint: Method, target: Package) {

    val vertices = mutableSetOf<Vertex>()

    private val traces = mutableSetOf<Trace>()

    private fun findInGraph(instruction: Instruction): Vertex? {
        if (isNotInGraph(instruction))
            return null
        return vertices.find { it.inst == instruction }
    }

    private fun isInGraph(instruction: Instruction): Boolean =
        Vert(instruction, mutableSetOf(), mutableSetOf()) in vertices

    private fun isNotInGraph(instruction: Instruction): Boolean = !isInGraph(instruction)

    private fun newVertexByInst(instruction: Instruction): Vertex = when (instruction) {
        is TerminateInst -> {
            TerminateVert(instruction, mutableSetOf(), mutableSetOf())
        }
        is CallInst -> {
            CallVert(instruction, mutableSetOf(), mutableSetOf())
        }
        else -> {
            Vert(instruction, mutableSetOf(), mutableSetOf())
        }
    }

    private fun Method.isInteresting() = when {
        this.isAbstract -> false
        this.isStaticInitializer -> false

        !this.hasBody -> false
        this.isConstructor -> false
        else -> true
    }

    private fun getAllOverrides(target: Package, method: Method): Set<Method> =
        method.cm.getAllSubtypesOf(method.`class`)
            .asSequence()
            .filterIsInstance<ConcreteClass>()
            .filter { target.isParent(it.`package`) }
            .map { it.getMethod(method.name, method.desc) }.filter { it.isInteresting() }
            .toSet()

    private fun addWeight(from: Vertex?, to: Vertex?, weight: Int): Boolean {
        if (from == null || to == null || weight <= -2  /*|| !from.successors.contains(to) */)
            return false
        from.weights[to] = weight
        from.successors.add(to)
        to.predecessors.add(from)
        return true
    }

    private fun wrapAndAddInst(inst: Instruction, predecessor: Vertex?): Vertex {

        val vert = findInGraph(inst) ?: newVertexByInst(inst)
        vertices.add(vert)

        if (predecessor == null)
            return vert
        vert.predecessors.add(predecessor)

        when (vert) {
            is TerminateVert -> {
                for (pred in vert.predecessors) {
                    if (vert.inst.isBranch())
                        addWeight(pred, vert, 1)
                    else
                        addWeight(pred, vert, 0)
                }

            }
            is CallVert -> {
                for (pred in vert.predecessors)
                    addWeight(pred, vert, 0)
            }

            is Vert -> {
                for (pred in vert.predecessors)
                    addWeight(pred, vert, 0)
            }
        }
        return vert
    }

    val rootMethod = enterPoint
    private val root: Vertex

    init {
        val temp = rootMethod.entry.first()
        root = wrapAndAddInst(temp, null)
        vertices.add(root)
        buildGraph(root, target)
    }

    private fun nextInst(instruction: Instruction): Instruction? {
        val iterator = instruction.parent.iterator()
        var result: Instruction? = null

        while (iterator.hasNext()) {
            result = iterator.next()
            if (result == instruction && iterator.hasNext()) {
                result = iterator.next()
                break
            }
        }
        return result
    }

    private fun buildGraph(start: Vertex, target: Package) {
        var current = mutableSetOf<Vertex>()
        current.add(start)
        var next = mutableSetOf<Vertex>()
        val visited = mutableSetOf<Vertex>()

        while (true) {
            current = current.filter { !visited.contains(it) }.toMutableSet()
            if (current.isEmpty())
                break

            for (vertex in current) {
                when (vertex) {
                    is TerminateVert -> {
                        val listWrapped = mutableListOf<Vertex>()
                        //for (successor in vertex.bb.successors) {
                        for (successor in vertex.inst.parent.successors) {
                            if (successor.instructions.isNullOrEmpty())
                                continue
                            listWrapped.add(wrapAndAddInst(successor.instructions.first(), vertex))
                        }
                        next.addAll(listWrapped)
                    }

                    is CallVert -> {
                        if (vertex.inst.method.isNotEmpty()) {
                            //next.add(wrapAndAddInst(vertex.inst.method.entry.first(), vertex))
                            val overrides = getAllOverrides(target, vertex.inst.method).filter { it.isNotEmpty() }
                            log.debug("overrides.size = ${overrides.size}")

                            overrides.forEach {
                                next.add(wrapAndAddInst(it.entry.first(), vertex))
                                log.debug("Graph: Wrapping method ${it.name} successful")
                            }

                        } else {
                            log.debug("Wrapping CallInst failed: method is empty")
                        }

                        val nextInst = nextInst(vertex.inst) ?: continue
                        next.add(wrapAndAddInst(nextInst, vertex))
                    }

                    else -> {
                        val inst = nextInst(vertex.inst) ?: continue
                        val wrapped = wrapAndAddInst(inst, vertex)
                        next.add(wrapped)
                    }
                }
                visited.add(vertex)
            }//current loop ends
            next = next.filter { !current.contains(it) }.toMutableSet()

            current = next
            next = mutableSetOf()
        }
        return
    }

    fun getTraces() = traces.toList()

    fun getTraces(depth: Int) = getTraces().filter { it.actions.size == depth }

    private fun bfsApply(start: Vertex, func: (Vertex) -> Unit) {
        val queue = queueOf(start)
        while (queue.isNotEmpty()) {
            val curr = queue.poll()
            func(curr)
            queue.addAll(curr.successors)
        }
    }

    private fun bfsFullApply(func: (Vertex) -> Unit) = bfsApply(root, func)

    fun Instruction.find() = vertices.find { it.inst == this }

    fun Instruction.findExcept(foundVertices: Set<Vertex>) =
        vertices.minus(foundVertices).find { it.inst == this }

    private fun coverStaticPath(actions: List<Action>): Boolean {
        var newBranchCovered = false
        var prevBlock: BasicBlock? = null
        var currentBlock: BasicBlock? = null

        for (action in actions) {
            when (action) {
                is MethodEntry -> {
                    continue
                }
                is MethodReturn -> {
                    continue
                }
                is MethodThrow -> {
                    continue
                }
                is MethodCall -> {
                    if (currentBlock != null && currentBlock.isNotEmpty) {
                        val temp = currentBlock.instructions.filterIsInstance<CallInst>()
                        val vert = temp.find { it.method == action.method }?.find()

                        if (vert != null /*&& prevBlock != null && prevBlock.isNotEmpty &&
                        prevBlock.terminator.isBranch()*/&& vert.isBranch() && !vert.isCovered
                        ) {
                            newBranchCovered = true
                        }
                        vert?.isCovered = true
                    }
                }
                is StaticInitEntry -> {
                    continue
                }
                is StaticInitExit -> {
                    continue
                }
                is BlockEntry -> {
                    prevBlock = currentBlock
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.instructions.first().find()

                    if (vert != null /*&& prevBlock != null && prevBlock.isNotEmpty &&
                        prevBlock.terminator.isBranch()*/&& vert.isBranch() && !vert.isCovered
                    ) {
                        newBranchCovered = true
                    }
                    vert?.isCovered = true
                }
                is BlockJump -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    for (inst in currentBlock.instructions) {
                        inst.find()?.isCovered = true
                    }
                    val vert = currentBlock.terminator.find()

                    if (vert != null && /*prevBlock != null && prevBlock.isNotEmpty &&
                        prevBlock.terminator.isBranch()*/vert.isBranch() && !vert.isCovered
                    ) {
                        newBranchCovered = true
                    }
                    vert?.isCovered = true
                }
                is BlockBranch -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.terminator.find() ?: continue
                    if (!vert.isCovered) {
                        newBranchCovered = true
                        vert.isCovered = true
                    }

                    /*if (prevBlock != null && prevBlock.isNotEmpty &&
                        prevBlock.terminator.isBranch() && !vert.isCovered
                    ) {
                        newBranchCovered = true
                        vert.isCovered = true
                    }*/

                    for (inst in currentBlock.instructions) {
                        inst.find()?.isCovered = true
                    }
                }
                is BlockSwitch -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.terminator.find() ?: continue
                    if (!vert.isCovered) {
                        newBranchCovered = true
                        vert.isCovered = true
                    }

                   /* if (prevBlock != null && prevBlock.isNotEmpty &&
                        prevBlock.terminator.isBranch() && !vert.isCovered
                    ) {
                        newBranchCovered = true
                        vert.isCovered = true
                    }*/

                    for (inst in currentBlock.instructions) {
                        inst.find()?.isCovered = true

                    }
                }
            }
        }
        return newBranchCovered
    }

    fun addTrace(trace: Trace): Boolean {
        traces.add(trace)
        val newBranchCovered = coverStaticPath(trace.actions)

        log.debug("Graph: trace added successfully, recomputing UD")
        recomputeUncoveredDistance()

        return newBranchCovered
    }

    private fun findUncovered(): MutableSet<Vertex> = vertices.filter { !it.isCovered }.toMutableSet()

    private fun recomputeUncoveredDistance() {
        val uncovered = findUncovered().filter { it.isBranch() }.toMutableSet()

        if (uncovered.isEmpty()) {
            log.info("Graph: No uncovered branches to recompute uncovered distance to")
            return
        }

        vertices.forEach { it.uncoveredDistance = Int.MAX_VALUE / 2 }

        for (vertex in uncovered) {
            if (vertex == this.root)
                continue

            //4 each vertex we generate a map that contains shortest paths to all that lies above it
            val map = dijkstra(vertex)
            val uncoveredKeys = map.keys.filter { uncovered.contains(it) }.toMutableSet()
            uncoveredKeys.forEach { map.keys.remove(it) }

            map.keys.forEach {
                if (it.uncoveredDistance >= map[it]!! && /*it.isBranch()*/ it.isBranchInst()) {
                    it.uncoveredDistance = map[it]!!
                    it.nearestUncovered = vertex
                }
            }
        }
        return
    }

    private fun Instruction.isBranch(): Boolean = this is BranchInst || this is SwitchInst || this is TableSwitchInst

    private fun Vertex.isBranchInst(): Boolean = this.inst.isBranch()

    private fun Vertex.isBranch(): Boolean {
        //if(this.isBranchInst()) return true
        if (this.predecessors.any { it.inst.isBranch() }) return true
        return false
    }

    private fun generateDijkstraSearchSet(v: Vertex): MutableSet<Vertex> {
        val result = mutableSetOf<Vertex>()
        var next = mutableSetOf<Vertex>()

        var current = mutableSetOf<Vertex>()
        current.add(v)
        result.add(v)
        while (current.isNotEmpty()) {
            for (vertex in current) {
                result.add(vertex)
                next.addAll(vertex.predecessors)
            }
            current = next.filter { !result.contains(it) }.toMutableSet()
            next = mutableSetOf()
        }
        current.remove(v)
        return result
    }

    private fun dijkstra(v: Vertex): MutableMap<Vertex, Int> {
        val q = mutableSetOf<Vertex>()            //set of unvisited
        val map = mutableMapOf<Vertex, Int>()
        var curr: Vertex

        q.add(v)
        q.addAll(generateDijkstraSearchSet(v))
        q.forEach { map[it] = Int.MAX_VALUE }
        map[v] = 0

        while (q.isNotEmpty()) {
            curr = q.first()

            for (neighbor in curr.predecessors) {
                val alt = map[curr]!! + neighbor.weights[curr]!!
                if (map[neighbor]!! >= alt) {
                    map[neighbor] = alt
                    neighbor.prev = curr
                }
            }
            q.remove(curr)
        }
        return map
    }

    //fun for editing our minUd set
    private fun checkUD(set: MutableSet<Vertex>, vertex: Vertex, ud: Int): MutableSet<Vertex> {
        if (vertex.uncoveredDistance + vertex.tries == ud) {
            set.add(vertex)
            return set
        }
        if (vertex.uncoveredDistance + vertex.tries < ud)
            return mutableSetOf(vertex)
        return set
    }

    private fun findWithMinUD(failed: MutableSet<Vertex>): MutableSet<Vertex> {
        var result = mutableSetOf<Vertex>()
        var ud = Int.MAX_VALUE
        val covered = vertices.filter { it.isCovered && !failed.contains(it) }

        for (vertex in covered) {
            if (failed.contains(vertex))
                continue
            result = if (vertex.isBranchInst() /*vertex.isBranch()*/)
                checkUD(result, vertex, ud)
            else
                result
            if (result.isNotEmpty())
                ud = result.first().uncoveredDistance
        }
        result = result.filter{ it.uncoveredDistance < Int.MAX_VALUE/2 }.toMutableSet()
        return result
    }

    fun nextBranchToForce(failed: MutableSet<Vertex>): Vertex? {
        val minUdSet = findWithMinUD(failed)
        return if (minUdSet.isEmpty())
            null
        else {
            minUdSet.random()
        }
    }

    suspend fun findPathsForSAP(curr: Vertex, ud: Int): MutableList<MutableList<Vertex>> {
        val start = mutableListOf(curr)
        val paths = findPathsDFS(curr, ud, start, mutableListOf(start))

        if (paths.isEmpty())
            return mutableListOf()

        val iterator = paths.iterator()
        while (iterator.hasNext()) {
            val path = iterator.next()
            val uncovered = path.filter { !it.isCovered }
            if (uncovered.isEmpty())
                iterator.remove()
            else {
                if (uncovered.count { it.isBranch() } < 1)
                    iterator.remove()
            }
        }
        return if (paths.isEmpty() || paths.count{it.size == 1} == paths.size)
            mutableListOf()
        else paths
    }

    private suspend fun findPathsDFS(
        curr: Vertex, ud: Int, path: MutableList<Vertex>,
        paths: MutableList<MutableList<Vertex>>
    ): MutableList<MutableList<Vertex>> {

        var updatedPaths = paths

        if (curr.successors.isEmpty()) {
            if (path.isEmpty())
                return updatedPaths

            updatedPaths.add(path)
            return updatedPaths
        }

        yield()

        for (successor in curr.successors) {
            val dist = ud - curr.weights[successor]!!
            if (dist < 0) {
                return updatedPaths
            }

            val newPath = mutableListOf<Vertex>()
            newPath.addAll(path)
            if (!newPath.contains(curr))
                newPath.add(curr)
            newPath.add(successor)

            updatedPaths = findPathsDFS(successor, dist, newPath, updatedPaths)
        }
        return updatedPaths
    }


    /**
     * We are moving higher from our purpose vertex to find a branch named $vertex successor that we should force
     * */
    private fun findSuccessor(vertex: Vertex): Vertex? {
        var purpose = vertex.nearestUncovered?: return null
        if(purpose in vertex.successors)
            return purpose

        var current = mutableSetOf(purpose)
        var next = mutableSetOf<Vertex>()
        val visited = mutableSetOf<Vertex>()
        while (current.isNotEmpty()) {
            current = current.filterNot { visited.contains(it) }.toMutableSet()
            for(v in current) {
                if (v.predecessors.contains(vertex)) {
                    return v
                }
                if(v.predecessors.isNotEmpty())
                    next.addAll(v.predecessors)
                visited.add(v)
            }
            current = next
            next = mutableSetOf()
        }
        return null
    }

    /**
     * Is used to find a static path to the vertex we want to be forced
     */
    fun getPathToBranch(vertex: Vertex): MutableList<Vertex>? {
        //vertex is a branchInst successor
//        if(!vertex.isBranch())
//            return null
        val successor = findSuccessor(vertex)
        if(successor == null){
            log.warn("Graph: couldn't find a path to force $vertex")
            return null
        }

        val result = mutableListOf(successor, vertex)

        var current = vertex

        if(current.predecessors.isEmpty())
            return null
        var next = current.predecessors.first()
        while(true) {
            current = next
            result.add(current)
            if(current.predecessors.isEmpty())
                break
            for(pred in current.predecessors) {
                if(result.contains(pred))
                    continue
                else
                    next = pred
            }
            if(next == current)
                return null
        }
        result.reverse()
        return result
    }

    //should be called if we are not analyzing graph due to problems with random trace
    fun countFullyUnreachable():Pair<Int, Int> {
        val blockSet = mutableSetOf<BasicBlock>()
        var blocks = 0
        var branches = 0

        val statistics = Statistics.invoke()

        vertices.forEach {
            if(!it.isCovered && it.inst.parent !in blockSet && statistics.inBlocks(it.inst.parent)) {
                blockSet += it.inst.parent
                blocks++
                if(it.isBranch())
                    branches++
            }
        }
        return Pair(blocks, branches)
    }


    fun dropTries() = vertices.forEach { it.tries = 0 }

}