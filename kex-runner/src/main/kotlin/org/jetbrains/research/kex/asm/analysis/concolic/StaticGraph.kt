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

        var tries: Int? = 0                                         //number of times branchWasNegated

        val terminateInst = this.bb.terminator


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


   /* private fun addMethod(method: Method, predecessor: Vert?): Vert? {
        val blocks = method.bodyBlocks
        val blockList = mutableListOf<BasicBlock>()
        blockList.addAll(blocks)

        var temp = method.entry

        var lastWrapped: Vert? = wrapAndAddBlock(temp, predecessor)

        while (blockList.isNotEmpty()) {
            temp = method.getNext(temp)
            lastWrapped = wrapAndAddBlock(temp, lastWrapped)
            blockList.minus(temp)
        }

        return lastWrapped
    }

    */


    private fun isInGraph(block: BasicBlock): Vert? {
        for(vertex in vertices) {
            if(vertex.bb == block)
                return vertex
        }
        return null
    }

    private fun wrapAndAddBlock(block: BasicBlock, predecessor: Vert?): Vert? {
        val pred = listOfNotNull(predecessor).toMutableSet()
        var vert: Vert? = isInGraph(block)

        for(inst in block.instructions) {
            if(inst is CallInst) {
                //TODO("If Block contains CallInst what r we doing?")
            }
        }

        if(vert == null) {
            vert = Vert(block, pred, mutableSetOf())
        }

        when (block.terminator) {
            is BranchInst -> {
                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 1) }
                for(successor in block.successors) {
                    wrapAndAddBlock(successor, vert)
                }
                return vert
            }

            is SwitchInst -> {
                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 0) }  //or weight 1?
                for(successor in block.successors){
                    wrapAndAddBlock(successor, vert)
                }
                return vert
            }

            is TableSwitchInst -> {
                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 0) }  //or weight 1?
                for(successor in block.successors){
                    wrapAndAddBlock(successor, vert)
                }
                return vert
            }

            is JumpInst -> {
                //TODO("What r we supposed 2 do")
                return vert
            }

            else -> {
                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 0) }
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
        /*
        var last: Vert? = null                                    //we should have used root here, but the resulting
        for(method in allMethods) {                                 //structure is gonna be fucked up
            last = addMethod(method, last)


        }
        */

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
        //TODO("comparison")
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

                if(key.bb.terminator is BranchInst && map[key]!! < dist) {
                    dist = map[key]!!
                    vert = key
                }
            }

            /* if(vert != null) {
                 vertex.uncoveredDistance = dist
                 vertex.nearestCovered = vert                                    //nearest covered BlockBranch
             }
             */

            if(vert != null) {
                if(dist < vert.uncoveredDistance) {
                    vert.uncoveredDistance = dist
                    vert.nearestUncovered = vertex
                }
            }

        }
        return
    }

    //SAME AS RECOMPUTE_UD

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
}