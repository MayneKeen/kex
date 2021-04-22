package org.jetbrains.research.kex.asm.analysis.concolic

import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.value.instruction.*

sealed class Vertex (open val inst: Instruction,
                                       open val predecessors: MutableCollection<Vertex>,
                                       open val successors: MutableCollection<Vertex>) {

    val weights = mutableMapOf<Vertex, Int>()
    var uncoveredDistance = Int.MAX_VALUE
    var isCovered = false
    var nearestUncovered: Vertex? = null //???
    var prev: Vertex? = null
    var tries = 0
    //val bb = this.inst.parent

    override fun hashCode(): Int {
        return (/*bb.hashCode() */inst.parent.hashCode() + inst.hashCode())
    }

    override fun equals(other: Any?): Boolean {
        return if (other is Vertex)
             //this.bb == other.bb && this.inst == other.inst
             this.inst.parent == other.inst.parent && this.inst == other.inst
        else false
    }

    override fun toString(): String {
        return inst.toString()
    }
}

data class Vert(override val inst: Instruction,
                    override val predecessors: MutableCollection<Vertex>,
                    override val successors: MutableCollection<Vertex>): Vertex(inst, predecessors, successors) {
    override fun equals(other: Any?): Boolean {
        if (other is Vertex)
            return super.equals(other)
        return false
    }

    override fun hashCode(): Int {
        return super.hashCode()
    }
}

data class CallVert(override val inst: CallInst,
                     override val predecessors: MutableCollection<Vertex>,
                     override val successors: MutableCollection<Vertex>): Vertex(inst, predecessors, successors) {
    override fun equals(other: Any?): Boolean {
        if (other is Vertex)
            return super.equals(other)
        return false
    }

    override fun hashCode(): Int {
        return super.hashCode()
    }
}


data class TerminateVert(override val inst: TerminateInst,
                        override val predecessors: MutableCollection<Vertex>,
                        override val successors: MutableCollection<Vertex>):Vertex(inst, predecessors, successors) {
    override fun equals(other: Any?): Boolean {
        if (other is Vertex)
            return super.equals(other)
        return false
    }

    override fun hashCode(): Int {
        return super.hashCode()
    }
}



