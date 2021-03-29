package org.jetbrains.research.kex.asm.analysis.concolic

import com.abdullin.kthelper.collection.queueOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.trace.`object`.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.*
import org.jetbrains.research.kfg.ir.value.instruction.*

class StaticGraph(val cm: ClassManager, enterPoint: Method) {

    private val vertices = mutableSetOf<Vertex>()
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

    private val rootMethod = enterPoint
    private val root: Vertex

    init {
        val temp = rootMethod.entry.first()
        root = wrapAndAddInst(temp, null)
        buildGraph(root)
    }

    private fun nextInst(instruction: Instruction): Instruction? {
//        if(instruction is TerminateInst)
//            return null
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
                        for (successor in vertex.bb.successors) {
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
                            log.debug("Wrapping CallInst ${vertex.inst} method" +
                                    "failed: method ${vertex.inst.method} is empty")
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
            vertices.minus(foundVertices).find { (it as Vertex).inst == this }

    private fun coverStaticPath(actions: List<Action>): Boolean {
        var newBranchCovered = false
        for (action in actions) {
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
                        temp.forEach { it.find()?.isCovered = true }
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
                    val vert = currentBlock.instructions.first().find()
                    vert?.isCovered = true
                }
                is BlockJump -> {
                    currentBlock = action.block
                    val vert = currentBlock.terminator.find()
                    vert?.isCovered = true
                }
                is BlockBranch -> {
                    currentBlock = action.block
                    val vert = currentBlock.terminator.find()
                    vert?.isCovered = true
                    newBranchCovered = true
                }
                is BlockSwitch -> {
                    currentBlock = action.block
                    val vert = currentBlock.terminator.find()
                    vert?.isCovered = true
                    newBranchCovered = true
                }
            }
        }
        return newBranchCovered
    }

    fun addTrace(trace: Trace): Boolean {
        traces.add(trace)
        val newBranchCovered = coverStaticPath(trace.actions)

        log.debug("graph: trace added successfully, recomputing UD")
        recomputeUncoveredDistance()
        log.debug("graph: just recomputed UD")
        return newBranchCovered
    }

    private fun findUncovered(): MutableSet<Vertex> = vertices.filter { it.isCovered }.toMutableSet()

    private fun recomputeUncoveredDistance() {
        val uncovered: MutableSet<Vertex> = findUncovered()

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
        if (vertex.uncoveredDistance == ud) {
            set.add(vertex)
            return set
        }
        if (vertex.uncoveredDistance < ud)
            return mutableSetOf(vertex)

        return set
    }

    private fun findWithMinUD(failed: MutableSet<Vertex>): MutableSet<Vertex> {
        var result = mutableSetOf<Vertex>()
        var ud = Int.MAX_VALUE

        val covered = vertices.filter { it.isCovered && !failed.contains(it) }.toMutableSet()

        for (vertex in covered)
            when (vertex) {
                is Vert -> {
                    continue
                }
                is CallVert -> {
                    continue
                }
                is TerminateVert -> {
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
                            continue
                        }
                    }
                    if (result.size == 1)
                        ud = result.first().uncoveredDistance
                }
            }
        return result
    }

    fun nextBranchToForce(failed: MutableSet<Vertex>): Vertex? {
        val minUdSet = findWithMinUD(failed)
        return if (minUdSet.isEmpty())
            null
        else {
            minUdSet.first()
        }
    }

    fun dropTries() = vertices.forEach { it.tries = 0 }

}