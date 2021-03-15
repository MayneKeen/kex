package org.jetbrains.research.kex.asm.analysis.concolic

import com.abdullin.kthelper.collection.queueOf
import com.abdullin.kthelper.collection.stackOf
import org.jetbrains.research.kex.trace.`object`.*


//CFG by AndreyBychkov https://github.com/AndreyBychkov
//plus my changes as WeightedTraceGraph

open class TraceGraph(startTrace: Trace) {

    data class Vertex(val action: Action,
                      val predecessors: MutableCollection<Vertex>,
                      val successors: MutableCollection<Vertex>) {

        val weights: MutableMap<Vertex, Int> = mutableMapOf()
        var uncoveredDistance: Int = 0

        var nearestCovered: Vertex? = null //???
        var nearestUncovered: Vertex? = null //???

        var prev: Vertex? = null

        var tries: Int? = 0

        override fun hashCode(): Int {
            return action.hashCode()
        }

        override fun equals(other: Any?): Boolean {
            if (other is Vertex)
                return this.action formalEquals other.action
            return false
        }

        override fun toString(): String {
            return action.toString()
        }
    }

    open class Branch(val actions: List<Action>) {
        fun context(len: Int) = Context(actions.takeLast(len))

        override fun equals(other: Any?): Boolean {
            if (other is Branch)
                return this.actions.zip(other.actions).map { (a, b) -> a formalEquals b }.all { it }
            return false
        }

        override fun hashCode(): Int {
            return actions.hashCode()
        }
    }

    class Context(actions: List<Action>) : Branch(actions)

    open fun toBranch(trace: Trace): Branch {
        return Branch(trace.actions)
    }

    open val vertices: MutableCollection<Vertex> = mutableSetOf()                                       //was not open
    val traces: MutableCollection<Trace> = mutableListOf()
    val rootToLeaf = mutableMapOf<Vertex, Vertex>()
    val leafToRoot
        get() = rootToLeaf.entries.associate { (k, v) -> v to k }
    var depth: Int = 0
        protected set                                                                                    //was private

    init { //TraceGraph(Trace startTrace) {
        traces.add(startTrace)
        val actionTail = startTrace.actions
        val root = Vertex(actionTail[0], mutableSetOf(), mutableSetOf())
        vertices.add(root)
        for (action in actionTail.drop(1)) {
            val currPred = vertices.last()
            val currVertex = Vertex(action, mutableSetOf(currPred), mutableSetOf())
            currPred.successors.add(currVertex)
            vertices.add(currVertex)
        }
        rootToLeaf[root] = vertices.last()
        depth = actionTail.size
    }

    fun getTraces(): List<Trace> {
        return traces.toList()
    }

    fun getTraces(depth: Int): List<Trace> {
        return getTraces().filter { it.actions.size == depth }
    }

    fun getTracesAndBranches(): List<Pair<Trace, Branch>> {
        val traces = getTraces()
        val branches = traces.map { toBranch(it) }
        return traces.zip(branches)
    }

    open fun addTrace(trace: Trace) {
        traces.add(trace)
        val methodStack = stackOf<MethodEntry>()
        val foundVerticesStack = stackOf<MutableSet<Vertex>>()
        var previousVertex: Vertex? = null
        trace.actions.forEach { action ->
            if (action is MethodEntry) {
                methodStack.push(action)
                foundVerticesStack.push(mutableSetOf())
            }
            // TODO:? Check if predecessor in same method

            val found = action.findExcept(foundVerticesStack.peek()) ?: wrapAndAddAction(action, previousVertex)
            val sameMethod = predecessorInSameMethod(found)
            // TODO:? Whats next?
            previousVertex?.successors?.add(found)
            found.predecessors.addAll(vertices.filter { found in it.successors })
            foundVerticesStack.peek().add(found)
            previousVertex = found

            if (action is MethodReturn && action.method == methodStack.peek().method) {
                methodStack.pop()
                foundVerticesStack.pop()
            }
        }
        rootToLeaf[trace.actions.first().find()!!] = trace.actions.last().find()!!
        depth = maxOf(depth, trace.actions.size)
    }

    protected fun predecessorInSameMethod(vertex: Vertex): Boolean {
        if(vertex.action is MethodEntry)
            return false
        return true
    }

    protected open fun wrapAndAddAction(action: Action, predecessor: Vertex?): Vertex {
        val pred = listOfNotNull(predecessor).toMutableSet()
        val vert = Vertex(action, pred, mutableSetOf())
        vertices.add(vert)
        return vert
    }

    protected fun bfsApply(start: Vertex, func: (Vertex) -> Unit) {
        val queue = queueOf(start)
        while (queue.isNotEmpty()) {
            val curr = queue.poll()
            func(curr)
            queue.addAll(curr.successors)
        }
    }

    protected fun bfsFullApply(func: (Vertex) -> Unit) {
        val visited = mutableSetOf<Vertex>()
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

    fun Action.find() = vertices.find { it.action formalEquals this }

    fun Action.findExcept(foundVertices: Set<Vertex>) = vertices.minus(foundVertices).find { it.action formalEquals this }

}

class DominatorTraceGraph(startTrace: Trace) : TraceGraph(startTrace) {
    private val dominatorMap = mutableMapOf<Vertex, Set<Vertex>>()
    private var nonDominatingVertices = setOf<Vertex>()

    init {
        update()
    }

    override fun toBranch(trace: Trace): Branch {
        return Branch(trace.actions.filter { act ->
            nonDominatingVertices.map { v -> v.action }
                    .any { v -> v formalEquals act }
        })
    }

    private fun update() {
        initRoots()
        updateDominatorMap()
        updateNonDominatingVertices()
    }

    private fun initRoots() {
        rootToLeaf.keys.forEach {
            dominatorMap[it] = setOf(it)
        }
    }

    private fun updateDominatorMap() {
        bfsFullApply {
            if (it.predecessors.isEmpty())
                updateDomMapRoots(it)
            else
                updateDomMapGeneral(it)
        }
    }

    private fun updateDomMapRoots(vertex: Vertex) {
        dominatorMap[vertex] = setOf(vertex)
    }

    private fun updateDomMapGeneral(vertex: Vertex) {
        dominatorMap[vertex] = vertex.predecessors
                .map { dominatorMap[it] ?: recoveryUpdateVertex(it) }
                .reduce { acc, set -> acc.intersect(set) }
                .union(setOf(vertex))
    }

    private fun recoveryUpdateVertex(vertex: Vertex): Set<Vertex> {
        updateDomMapGeneral(vertex)
        return dominatorMap[vertex]!!
    }

    private fun updateNonDominatingVertices() {
        nonDominatingVertices = vertices.filter { vert -> vert.dominatesOnlyItself() }.toSet()
    }

    private fun Vertex.dominatesOnlyItself(): Boolean {
        return dominatorMap.filterValues { doms -> this in doms }.size == 1
    }

    override fun addTrace(trace: Trace) {
        super.addTrace(trace)
        update()
    }
}

/*

class WeightedTraceGraph(startTrace: Trace): TraceGraph(startTrace) {

    init {
        this.traces.add(startTrace)
        val actionTail = startTrace.actions
        val root = Vertex(actionTail[0], mutableSetOf(), mutableSetOf())
        this.vertices.add(root)

        for (action in actionTail.drop(1)) {
            val currPred = vertices.last()

            val currVertex = Vertex(action, mutableSetOf(currPred), mutableSetOf())

            if(currVertex.action is BlockBranch) {
                addEdgeWithWeight(currPred, currVertex, 1)
            }
            else {
                addEdgeWithWeight(currPred, currVertex, 0)
            }
            vertices.add(currVertex)
        }
        rootToLeaf[root] = vertices.last()
        depth = actionTail.size
    }


    //maybe I should change this later
    private fun addEdgeWithWeight(from: Vertex?, to: Vertex?, weight: Int): Boolean {
        if ( from == null || to == null || weight<=-2  /*|| !from.successors.contains(to) */)
            return false
        from.weights[to] = weight
        from.successors.add(to)
        return true
    }

    override fun wrapAndAddAction(action: Action, predecessor: Vertex?): Vertex {
        val pred = listOfNotNull(predecessor).toMutableSet()
        val vert = Vertex(action, pred, mutableSetOf())

        if(action is BlockBranch)
            addEdgeWithWeight(predecessor, vert, 1)
        else
            addEdgeWithWeight(predecessor, vert, 0)

        vertices.add(vert)
        return vert
    }


    override fun addTrace(trace: Trace) {
        traces.add(trace)
        val methodStack = stackOf<MethodEntry>()
        val foundVerticesStack = stackOf<MutableSet<Vertex>>()
        var previousVertex: Vertex? = null
        trace.actions.forEach { action ->
            if (action is MethodEntry) {
                methodStack.push(action)
                foundVerticesStack.push(mutableSetOf())
            }

            val found = action.findExcept(foundVerticesStack.peek()) ?: wrapAndAddAction(action, previousVertex)  //may cause NullPointer
            val sameMethod = predecessorInSameMethod(found)
            // TODO:? Whats next?

            if(found.action is BlockBranch)
                addEdgeWithWeight(previousVertex, found, 1)
            else
                addEdgeWithWeight(previousVertex, found, 0)

            found.predecessors.addAll(vertices.filter { found in it.successors })
            foundVerticesStack.peek().add(found)
            previousVertex = found

            if (action is MethodReturn && action.method == methodStack.peek().method) {
                methodStack.pop()
                foundVerticesStack.pop()
            }
        }
        rootToLeaf[trace.actions.first().find()!!] = trace.actions.last().find()!!
        depth = maxOf(depth, trace.actions.size)
    }

    fun recomputeUncoveredDistance() {
        val uncoveredBranches: MutableSet<Vertex> = findUncoveredBranches()
        for(vertex in uncoveredBranches){
            val map = dijkstra(vertex)
            var dist = Int.MAX_VALUE
            var vert: Vertex? = null

            for(key: Vertex in map.keys) {
                if(uncoveredBranches.contains(key))
                    continue

                if(key.action is BlockBranch && map[key]!! < dist) {
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

    private fun findUncoveredBranches(): MutableSet<Vertex> {
        val result: MutableSet<Vertex> = mutableSetOf()

        for(vertex in vertices) {
            result.add(vertex)
            traces.forEach {
                if (it.contains(vertex))
                    result.remove(vertex)
            }
        }
        return result
    }

    private fun dijkstra(v: Vertex): MutableMap<Vertex, Int> {
        val q = mutableSetOf<Vertex>()
        val map = mutableMapOf<Vertex, Int >()
        var u: Vertex = v

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

    /*
    fun solveAlongPath() {                       //(p: path (execution), p(i): (branch on p), S: (path along CFG) ) =
                                                 // = q: [p(0)..p(i-1) = q(..i-1)], [q(i..) matches S]

    }
    */

}

 */