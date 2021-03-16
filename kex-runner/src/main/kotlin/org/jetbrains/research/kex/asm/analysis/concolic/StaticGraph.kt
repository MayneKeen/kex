package org.jetbrains.research.kex.asm.analysis.concolic

import com.abdullin.kthelper.collection.queueOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.trace.`object`.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.*
import org.jetbrains.research.kfg.ir.value.instruction.*


class StaticGraph(val cm: ClassManager, val enterPoint: Method) {


    data class Vert(val bb: BasicBlock,
                    val predecessors: MutableCollection<Vert>,
                    val successors: MutableCollection<Vert>) {

        val weights: MutableMap<Vert, Int> = mutableMapOf()
        var uncoveredDistance: Int = Int.MAX_VALUE

        var isCovered = false

        var nearestCovered: Vert? = null //???
        var nearestUncovered: Vert? = null //???

        var prev: Vert? = null

        var tries: Int = 0                                         //number of times branchWasNegated
        val terminateInst = this.bb.terminator
        var callInst: Instruction? = null

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
        private set


    private fun isInGraph(block: BasicBlock): Vert? {
        for(vertex in vertices) {
            if(vertex.bb == block)
                return vertex
        }
        return null
    }

    private fun wrapAndAddBlock(block: BasicBlock, predecessor: Vert?): Vert {
        val pred = listOfNotNull(predecessor).toMutableSet()
        var vert: Vert? = isInGraph(block)

        if(vert == null) {
            vert = Vert(block, pred, mutableSetOf())
        }
/*
        for(inst in block.instructions) {
            if(inst is CallInst) {
                val clonedVert = Vert(block, pred, mutableSetOf())
                clonedVert.callInst = inst
                addEdgeWithWeight(clonedVert, predecessor, 0)
                vertices.add(vert)
            }
        }
 */
        when (block.terminator) {
            is BranchInst -> {
                //log.debug("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
                //log.debug("WOW< FOUND A BRANCHINST")
                //log.debug("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")

                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 1) }
                vertices.add(vert)
                for(successor in block.successors) {
                    wrapAndAddBlock(successor, vert)
                }
                return vert
            }

            is SwitchInst -> {
                //log.debug("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
                //log.debug("WOW< FOUND A SWITCHINST")
                //log.debug("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")

                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 1) }
                vertices.add(vert)
                for(successor in block.successors){
                    wrapAndAddBlock(successor, vert)
                }
                return vert
            }

            is TableSwitchInst -> {
                //log.debug("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
                //log.debug("WOW< FOUND A TABLESWITCHINST")
                //log.debug("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")

                vert.predecessors.forEach { addEdgeWithWeight(it, vert, 1) }
                vertices.add(vert)
                for(successor in block.successors){
                    wrapAndAddBlock(successor, vert)
                }
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

    init {          //val cm: ClassManager, val enterPoint: Method

        rootMethod = enterPoint
        root = wrapAndAddBlock(rootMethod.entry, null)
        vertices.add(root)

        val concreteClasses = cm.concreteClasses
        val allMethods: MutableSet<Method> = mutableSetOf()
        concreteClasses.forEach { allMethods.addAll(it.allMethods) }

        root.bb.successors.forEach{ addBlocks(it, root) }

    }

    private fun addBlocks(bb: BasicBlock, predecessor: Vert?) {
        //wrapping the first block to start with non-null pred
        var pred = wrapAndAddBlock(bb, predecessor)

        //blocks to add during current iteration
        val current = mutableMapOf<Vert, LinkedHashSet<BasicBlock>>()
        //blocks to add during the next iteration
        val next = mutableMapOf<Vert, LinkedHashSet<BasicBlock>>()

        val visited = mutableSetOf<BasicBlock>()

        current[pred] = pred.bb.successors
        visited.add(pred.bb)

        while(true) {
            val currentIterator = current.keys.iterator()

            while(currentIterator.hasNext()) {
                val key = currentIterator.next()

                //check if our vertex was already visited
                if(visited.contains(key.bb) && key.bb != pred.bb && key.bb != predecessor?.bb) {
                    currentIterator.remove()
                    log.debug("GRAPH: addBlocks: removed an already visited element")
                    continue
                }

                val value = current[key]
                if(value.isNullOrEmpty()) {
                    currentIterator.remove()
                    continue
                }

                for(element in value) {
                    val previous = wrapAndAddBlock(element, key)
                    next[previous] = previous.bb.successors

                    //putting another methods into next using CallInst's and JumpInst's succesors
                    for(inst in element.instructions) {
                        if(inst is CallInst && !inst.method.isEmpty()) {
                            val temp = inst.method.entry
                            if(next[previous].isNullOrEmpty())
                                next[previous] = linkedSetOf(temp)
                            else
                                next[previous]?.add(temp)
                        }

                        else if(inst is JumpInst && !element.successors.contains(inst.successor)) {
                            val temp = inst.successor
                            if(next[previous].isNullOrEmpty())
                                next[previous] = linkedSetOf(temp)
                            else
                                next[previous]?.add(temp)
                        }

                    }
                    /*log.debug("block : $element")
                    log.debug("successors : " + next[previous]) */
                }
                visited.add(key.bb)
                currentIterator.remove()
            }
            //here current is supposed to be empty
            current.putAll(next)
            if(current.isEmpty())
                break

            next.keys.removeAll(next.keys)
        }
        return
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

    //adds a trace to our graph and
    // returns true if it contains a previously uncovered branch
    fun addTrace(trace: Trace): Boolean {
        traces.add(trace)
        log.debug("Graph: adding a trace")
        var newBranchCovered = false
        for(action in trace.actions)
            for(vert in vertices)
                if(actionEqualsBB(action, vert.bb))
                    if(!vert.isCovered)
                        when(vert.terminateInst) {
                            is BranchInst -> {
                                newBranchCovered = true
                                vert.isCovered = true
                            }
                            is SwitchInst -> {
                                newBranchCovered = true
                                vert.isCovered = true
                            }
                            is TableSwitchInst -> {
                                newBranchCovered = true
                                vert.isCovered = true
                            }
                            else -> {
                                vert.isCovered = true
                            }
                        }
        log.debug("graph: trace added successfully, recomputing UD")
        recomputeUncoveredDistance()
        log.debug("graph: just recomputed UD")
        return newBranchCovered
    }


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
            if(!vertex.isCovered)
                result.add(vertex)
        }
        return result
    }

    private fun recomputeUncoveredDistance() {
        val uncovered: MutableSet<Vert> = findUncovered()
        val covered = vertices.filter { !uncovered.contains(it) }.toMutableSet()

        val mapList = mutableListOf<MutableMap<Vert, Int>>()

        for(vertex in uncovered) {
            if(vertex == this.root) {
                continue
            }
            //distances 4 everything that lies above our uncovered vertex
            val map = dijkstra(vertex)

            val uncoveredKeys = map.keys.filter{ uncovered.contains(it) }.toMutableSet()
            uncoveredKeys.forEach { map.keys.remove(it) }
            //here map shoul contain only covered vertices and distances to them from our uncovered vertex

            var temp = map.keys.first()

            map.keys.forEach {
                if(it.uncoveredDistance >= map[it]!!) {
                    it.uncoveredDistance = map[it]!!
                    it.nearestUncovered = vertex
                }
            }
        }
        return
    }

    //generates Set<Vert> of everything that lies above v: Vert
    private fun generateDijkstraSearchSet(v: Vert): MutableSet<Vert> {
        val result = mutableSetOf<Vert>()
        val next = mutableSetOf<Vert>()

        var current = mutableSetOf<Vert>()
        current.add(v)

        while(current.isNotEmpty()) {

            for(vertex in current) {
                result.add(vertex)
                next.addAll(vertex.predecessors)
            }

            current.addAll(next)
            current = current.filter { !result.contains(it) }.toMutableSet()
            next.removeAll(current)
        }
        current.remove(v)
        return result
    }

    private fun dijkstra(v: Vert): MutableMap<Vert, Int> {
        val q = mutableSetOf<Vert>()            //set of unvisited
        val map = mutableMapOf<Vert, Int >()
        var curr: Vert

        q.add(v)

        val searchSet = generateDijkstraSearchSet(v)

        q.addAll(searchSet)
        q.forEach { map[it] = Int.MAX_VALUE }

        while (q.isNotEmpty()) {
            curr = q.first()

            for(neighbor in curr.predecessors) {
                val alt = map[curr]!! + neighbor.weights[curr]!!
                if(map[neighbor]!! >= alt) {
                    map[neighbor] = alt
                    neighbor.prev = curr
                }
            }
            q.remove(curr)
        }
        return map
    }

    private fun findVertByBB(bb: BasicBlock): Vert? {
        for(vertex in vertices) {
            if(vertex.bb == bb)
                return vertex
        }
        return null
    }

    private fun findWithMinUD(trace: Trace, failed: MutableSet<Vert>): MutableList<Vert> {
        val result = mutableListOf<Vert>()
        var ud = Int.MAX_VALUE

        //we're gettin a list containing all of the BlockActions from our trace
        //vertices in failed Set will be ignored
        for(action in trace.actions) {
            if(action is BlockAction){
                val vert = findVertByBB(action.block)

                if(vert != null && !failed.contains(vert)) {
                    result.add(vert)
                    if(vert.uncoveredDistance + vert.tries < ud )
                        ud = vert.uncoveredDistance + vert.tries
                }
                else
                    continue
            }
        }

        //then we search for minimum UD among our branches
        val iterator = result.iterator()
        while(iterator.hasNext()) {
            val vert = iterator.next()
            if (!(vert.terminateInst is BranchInst
                            || vert.terminateInst is SwitchInst
                            || vert.terminateInst is TableSwitchInst)) {
                iterator.remove()
                continue
            }
            else {
                log.debug("=============================================================================================")
                log.debug("=============================================================================================")
                log.debug("IM FINALLY DOING MY JOB")
                log.debug("=============================================================================================")
                log.debug("=============================================================================================")
            }
            if (vert.uncoveredDistance + vert.tries > ud)
                iterator.remove()
        }
        return result
    }

    //returns a branch with min UncoveredDistance for a trace
    fun findBranchForSAP(trace: Trace, failed: MutableSet<Vert>): Vert? {
        val list = findWithMinUD(trace, failed)
        if(list.isEmpty())
            return null

        return list[0]
    }

    //returns next branch according to our algorithm to be forced by cfgds
    fun nextBranchToForce(failed: MutableSet<Vert>): Vert? {
        var result: Vert? = null
        for(trace in traces) {
            val temp = findBranchForSAP(trace, failed) ?: continue
            if(result == null)
                result = temp
            if(result.uncoveredDistance + result.tries > temp.uncoveredDistance + temp.tries)
                result = temp
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