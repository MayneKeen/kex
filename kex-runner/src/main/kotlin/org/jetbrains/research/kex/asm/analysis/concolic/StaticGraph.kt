package org.jetbrains.research.kex.asm.analysis.concolic

import com.abdullin.kthelper.collection.queueOf
import org.jetbrains.research.kex.asm.analysis.concolic.TraceGraph.*
import org.jetbrains.research.kex.trace.`object`.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.*
import org.jetbrains.research.kfg.ir.value.instruction.*


class StaticGraph(val cm: ClassManager, val startTrace: Trace, val enterPoint: Method) {


    data class Vert(val bb: BasicBlock,
                    val predecessors: MutableCollection<Vert>,
                    val successors: MutableCollection<Vert>) {

        val weights: MutableMap<Vert, Int> = mutableMapOf()
        var uncoveredDistance: Int = 0

        var nearestCovered: Vert? = null //???
        var nearestUncovered: Vert? = null //???

        var prev: Vert? = null

        var tries: Int = 0                                         //number of times branchWasNegated

        val terminateInst = this.bb.terminator

        val callInst: Instruction? = null

        override fun hashCode(): Int {
            return bb.hashCode()
        }

        override fun equals(other: Any?): Boolean {
            if (other is Vert)
                return this.bb == other.bb
            return false
        }

        override fun toString(): String {
            return bb.toString()
        }
    }


    open val vertices: MutableCollection<Vert> = mutableSetOf()

    private val traces: MutableCollection<Trace> = mutableSetOf()

    val rootToLeaf = mutableMapOf<Vert, Vert>()
    val leafToRoot
        get() = rootToLeaf.entries.associate { (k, v) -> v to k }
    var depth: Int = 0
        protected set


    private fun isInGraph(block: BasicBlock): Vert? {
        for(vertex in vertices) {
            if(vertex.bb == block)
                return vertex
        }
        return null
    }


    //I M P O R T A N T

    //could use vertices.add(vert)
    //for every addEdgeWithWeight in here

    private fun wrapAndAddBlock(block: BasicBlock, predecessor: Vert?): Vert? {
        val pred = listOfNotNull(predecessor).toMutableSet()
        var vert: Vert? = isInGraph(block)

        if(vert == null) {
            vert = Vert(block, pred, mutableSetOf())
        }

        for(inst in block.instructions) {
            if(inst is CallInst) {
                val clonedVert = Vert(block, pred, mutableSetOf())
                addEdgeWithWeight(clonedVert, predecessor, 0)
                vertices.add(vert)
            }
        }

        when (block.terminator) {
            is BranchInst -> {
                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 1) }
                for(successor in block.successors) {
                    wrapAndAddBlock(successor, vert)
                }
                vertices.add(vert)
                return vert
            }

            is SwitchInst -> {
                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 1) }
                for(successor in block.successors){
                    wrapAndAddBlock(successor, vert)
                }
                vertices.add(vert)
                return vert
            }

            is TableSwitchInst -> {
                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 1) }
                for(successor in block.successors){
                    wrapAndAddBlock(successor, vert)
                }
                vertices.add(vert)
                return vert
            }

            else -> {
                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 0) }
                vertices.add(vert)
                return vert
            }
        }


    }

    private var rootMethod: Method
    private var root: Vert

    init {          //val cm: ClassManager, val startTrace: Trace, val enterPoint: Method
        addTrace(startTrace)

        rootMethod = enterPoint
        root = wrapAndAddBlock(rootMethod.entry, null)!!
        vertices.add(root)

        val concreteClasses = cm.concreteClasses
        val allMethods: MutableSet<Method> = mutableSetOf()
        concreteClasses.forEach { allMethods.addAll(it.allMethods) }

        root.bb.successors.forEach{ recursiveAdd(it, root) }

    }
    private fun recursiveAdd(bb: BasicBlock, predecessor: Vert?) {
        var curr = bb
        var pred = predecessor

        pred = wrapAndAddBlock(curr, pred)
        for(successor in curr.successors) {
            recursiveAdd(successor, pred)
        }
    }

    fun getTraces(): List<Trace> {
        return traces.toList()
    }

    fun getTraces(depth: Int): List<Trace> {
        return getTraces().filter { it.actions.size == depth }
    }


    private fun bfsApply(start: Vert, func: (Vert) -> Unit) {
        val queue = queueOf(start)
        while (queue.isNotEmpty()) {
            val curr = queue.poll()
            func(curr)
            queue.addAll(curr.successors)
        }
    }

    private fun bfsFullApply(func: (Vert) -> Unit) {
        val visited = mutableSetOf<Vert>()
        val queue = queueOf(rootToLeaf.keys)
        while (queue.isNotEmpty()) {
            val curr = queue.poll()
            if (curr in visited)
                continue
            func(curr)
            visited.add(curr)
            queue.addAll(curr.successors)
        }
    }

    fun BasicBlock.find() = vertices.find { it.bb == this }

    fun BasicBlock.findExcept(foundVertices: Set<Vert>) = vertices.minus(foundVertices).find { it.bb == this }


    fun addTrace(trace: Trace) = traces.add(trace)

    private fun addEdgeWithWeight(from: Vert?, to: Vert?, weight: Int): Boolean {
        if ( from == null || to == null || weight<=-2  /*|| !from.successors.contains(to) */)
            return false
        from.weights[to] = weight
        from.successors.add(to)
        to.predecessors.add(from)
        return true
    }


    private fun actionEqualsBB(action: Action, bb: BasicBlock): Boolean {
        if(action is BlockAction)
            return action.block == bb
        return false
    }


    private fun findUncovered(): MutableSet<Vert> {
        val result: MutableSet<Vert> = mutableSetOf()

        for(vertex in vertices) {
            result.add(vertex)
            traces.forEach {
                for(action in it)
                    if(actionEqualsBB(action, vertex.bb))
                        result.remove(vertex)
            }
        }
        return result
    }

    fun recomputeUncoveredDistance() {
        val uncoveredBranches: MutableSet<Vert> = findUncovered()
        for(vertex in uncoveredBranches){
            val map = dijkstra(vertex)
            var dist = Int.MAX_VALUE
            var vert: Vert? = null

            for(key: Vert in map.keys) {
                if(uncoveredBranches.contains(key))
                    continue

                if((key.terminateInst is BranchInst
                                || key.terminateInst is SwitchInst
                                || key.terminateInst is TableSwitchInst)
                        && map[key]!! < dist) {
                    dist = map[key]!!
                    vert = key
                }
            }

            if(vert != null) {
                if(dist < vert.uncoveredDistance) {
                    vert.uncoveredDistance = dist
                    vert.nearestUncovered = vertex
                }
            }

        }
        return
    }

    private fun dijkstra(v: Vert): MutableMap<Vert, Int> {
        val q = mutableSetOf<Vert>()
        val map = mutableMapOf<Vert, Int >()
        var u: Vert = v

        q.add(v)
        v.uncoveredDistance = 0
        map[v] = 0

        for(vertex in vertices) {
            if(vertex == v)
                continue
            q.add(vertex)
            map[vertex] = Int.MAX_VALUE
        }

        while (q.isNotEmpty()) {
            for(vertex in q){
                if(map[vertex]!! < map[u]!!)
                    u = vertex
            }
            q.remove(u)

            for(pred in u.predecessors) {
                var alt = map[u]!! + pred.weights[u]!!

                if(alt < map[pred]!!) {
                    map[pred] = alt
                    pred.prev = u
                }
            }
        }
        return map
    }

    fun findVertByBB(bb: BasicBlock): Vert? {
        for(vertex in vertices) {
            if(vertex.bb == bb)
                return vertex
        }
        return null
    }

    fun findWithMinUD(trace: Trace): MutableList<Vert> {
        val result = mutableListOf<Vert>()
        var ud = Int.MAX_VALUE

        //we're gettin a list containing all of the BlockActions in our trace out of here
        for(action in trace.actions) {
            if(action is BlockAction){
                val vert = findVertByBB(action.block)
                if(vert != null) {
                    result.add(vert)
                    if(vert.uncoveredDistance < ud)
                        ud = vert.uncoveredDistance
                }
            }
        }

        //then we search for minimum UD among our branches
        for(vert in result) {
            if (!(vert.terminateInst is BranchInst
                            || vert.terminateInst is SwitchInst
                            || vert.terminateInst is TableSwitchInst)) {
                result.remove(vert)
                continue
            }
            if (vert.uncoveredDistance > ud)
                result.remove(vert)

        }
        return result
    }


    fun dropTries() {
        for (vertex in vertices) {
            vertex.tries = 0
        }
        return
    }

}