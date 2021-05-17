package org.jetbrains.research.kex.asm.analysis.concolic

import org.jetbrains.research.kthelper.collection.queueOf
import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.trace.`object`.*
import org.jetbrains.research.kfg.ir.*
import org.jetbrains.research.kfg.ir.value.instruction.*

class StaticGraph(enterPoint: Method) {

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
                val isBranch = (vert.inst is BranchInst || vert.inst is SwitchInst || vert.inst is TableSwitchInst)
                for (pred in vert.predecessors) {
                    if (isBranch)
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
        buildGraph(root)
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

    private fun buildGraph(start: Vertex) {
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
                        if (vertex.inst.method.isNotEmpty())
                            next.add(wrapAndAddInst(vertex.inst.method.entry.first(), vertex))
                        else {
                            log.debug("Wrapping CallInst failed: method is empty")
                        }
                    }

                    else -> {
                        val inst = nextInst(vertex.inst) ?: continue
                        val wrapped = wrapAndAddInst(inst, vertex)
                        next.add(wrapped)
                    }
                }
                visited.add(vertex)
            }//current loop ends

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
        var prev:Vertex? = null
        var currentBlock: BasicBlock? = null
        for (action in actions) {
            when (action) {
                is MethodEntry -> {
                    if (action.method.hasBody) {
                        currentBlock = action.method.entry
                        currentBlock.instructions.first().find()?.isCovered = true
                    }
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
                        val vert = temp.find { it.method == action.method }?.find()

                        if(vert != null && prev != null && prev is TerminateVert &&
                            (prev.inst is BranchInst || prev.inst is SwitchInst || prev.inst is TableSwitchInst)
                            && !vert.isCovered) {
                            newBranchCovered = true
                        }
                        vert?.isCovered = true
                        prev = vert
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
                    val vert = currentBlock.instructions.first().find()

                    if(vert != null && prev != null && prev is TerminateVert &&
                        (prev.inst is BranchInst || prev.inst is SwitchInst || prev.inst is TableSwitchInst)
                        && !vert.isCovered) {
                        newBranchCovered = true
                    }
                    vert?.isCovered = true
                    prev = vert
                }
                is BlockJump -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    for (inst in currentBlock.instructions) {
                        inst.find()?.isCovered = true
                    }
                    val vert = currentBlock.terminator.find()
                    if(vert != null && prev != null && prev is TerminateVert &&
                        (prev.inst is BranchInst || prev.inst is SwitchInst || prev.inst is TableSwitchInst)
                        && !vert.isCovered) {
                        newBranchCovered = true
                    }
                    vert?.isCovered = true
                    prev = vert
                }
                is BlockBranch -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.terminator.find() ?: continue
                    if (!vert.isCovered) {
                        newBranchCovered = true
                    }
                    for (inst in currentBlock.instructions) {
                        inst.find()?.isCovered = true
                    }
                    prev = vert
                }
                is BlockSwitch -> {
                    currentBlock = action.block
                    if (currentBlock.isEmpty)
                        continue
                    val vert = currentBlock.terminator.find() ?: continue
                    if (!vert.isCovered) {
                        newBranchCovered = true
                    }
                    for (inst in currentBlock.instructions) {
                        inst.find()?.isCovered = true
                    }
                    prev = vert
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
        val uncovered: MutableSet<Vertex> = findUncovered()

        vertices.forEach { it.uncoveredDistance = Int.MAX_VALUE / 2 }

        for (vertex in uncovered) {
            if (vertex == this.root)
                continue
            val map = dijkstra(vertex)
            val uncoveredKeys = map.keys.filter { uncovered.contains(it) }.toMutableSet()
            uncoveredKeys.forEach { map.keys.remove(it) }

            map.keys.forEach {
                if (it.uncoveredDistance >= map[it]!!) {
                    it.uncoveredDistance = map[it]!!
                    it.nearestUncovered = vertex
                }
            }
        }
        return
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

    private fun findWithMinUD(failed: MutableSet<Vertex>/*, forced: MutableSet<Vertex>*/): MutableSet<Vertex> {
        log.debug("Graph: entering findWithMinUd")
        var result = mutableSetOf<Vertex>()
        var ud = Int.MAX_VALUE

        val covered = vertices.filter { it.isCovered && !failed.contains(it) /*&& forced.contains(it)*/ }
            .filterIsInstance<TerminateVert>().toMutableSet()

        //4 debug only {
        val instances = covered.filter { it.inst is BranchInst || it.inst is SwitchInst || it.inst is TableSwitchInst }
        val total = vertices.filterIsInstance<TerminateVert>()
            .filter { it.inst is BranchInst || it.inst is SwitchInst || it.inst is TableSwitchInst }
        log.debug("Graph: findWithMinUd covered terminators quantity = (" + covered.size + ")")
        log.debug("Graph: Total branches quantity = (" + total.size + ")")
        log.debug("Graph: findWithMinUd covered branches quantity = (" + instances.size + ")")
        //{

        for (vertex in covered) {
            result = when (vertex.inst) {
                is BranchInst -> {
                    checkUD(result, vertex, ud)
                }
                is SwitchInst -> {
                    checkUD(result, vertex, ud)
                }
                is TableSwitchInst -> {
                    checkUD(result, vertex, ud)
                }
                else -> {
                    result
                    continue
                }

            }
            if (result.isNotEmpty())
                ud = result.first().uncoveredDistance
        }
        return result
    }

    fun nextBranchToForce(failed: MutableSet<Vertex>/*, forced: MutableSet<Vertex>*/): Vertex? {
        val minUdSet = findWithMinUD(failed/*, forced*/)
        return if (minUdSet.isEmpty())
            null
        else {
            minUdSet.iterator().next()
        }
    }

    fun findPathsForSAP(curr: Vertex, ud: Int): MutableList<MutableList<Vertex>> {
        val paths = findPathsDFS(curr, ud, mutableListOf(), mutableListOf())

        if (paths.isEmpty())
            return mutableListOf()

        val iterator = paths.iterator()
        while (iterator.hasNext()) {
            val path = iterator.next()
            val uncoveredSet = path.filter { !it.isCovered }.toMutableSet()
            if (uncoveredSet.isNullOrEmpty()) {
                iterator.remove()
            }
        }
        return if (paths.isEmpty())
            mutableListOf()
        else paths
    }

    private fun findPathsDFS(
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

        for (successor in curr.successors) {
            val dist = ud - curr.weights[successor]!!
            print("dist is $dist")
            print("${path.size}")
            if (dist < 0) {
                return updatedPaths
            }

            val newPath = mutableListOf<Vertex>()
            newPath.addAll(path)
            if(!newPath.contains(curr))
                newPath.add(curr)
            newPath.add(successor)

            updatedPaths = findPathsDFS(successor, dist, newPath, updatedPaths)
        }
        return updatedPaths
    }

    fun dropTries() = vertices.forEach { it.tries = 0 }

}