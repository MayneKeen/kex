package org.jetbrains.research.kex.trace.`object`

import org.jetbrains.research.kex.asm.analysis.concolic.Statistics
import org.jetbrains.research.kex.asm.manager.CoverageInfo
import org.jetbrains.research.kex.asm.manager.isUnreachable
import org.jetbrains.research.kex.asm.manager.originalBlock
import org.jetbrains.research.kthelper.assert.unreachable
import org.jetbrains.research.kthelper.collection.stackOf
import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.trace.TraceManager
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.BranchInst
import org.jetbrains.research.kfg.ir.value.instruction.SwitchInst
import org.jetbrains.research.kfg.ir.value.instruction.TableSwitchInst

class ObjectTraceManager : TraceManager<Trace> {
    private val methodInfos = mutableMapOf<Method, MutableSet<Trace>>()
    private val fullTraces = mutableSetOf<Trace>()

    private var coveredBlocksCnt = 0
    private var coveredBranchesCnt = 0

    private val alrCoveredBlocks = mutableListOf<BasicBlock>()
    private val alrCoveredBranches = mutableListOf<BasicBlock>()

    override fun getTraces(method: Method): List<Trace> = methodInfos.getOrDefault(method, mutableSetOf()).toList()

    override fun addTrace(method: Method, trace: Trace) {
        val methods = mutableListOf<Method>()
        for(action in trace)
            if(action is MethodEntry)
                methods.add(action.method)
        setAlrCovered(methods)

        fullTraces += trace
        val traceStack = stackOf<MutableList<Action>>()
        val methodStack = stackOf<Method>()

        for (action in trace) {
            when (action) {
                is MethodEntry -> {
                    traceStack.push(mutableListOf(action))
                    methodStack.push(action.method)
                }
                is StaticInitEntry -> {
                    traceStack.push(mutableListOf(action))
                    methodStack.push(action.method)
                }
                is MethodReturn, is MethodThrow, is StaticInitExit -> {
                    val methodTrace = traceStack.pop()
                    methodTrace += action
                    methodInfos.getOrPut(methodStack.pop(), ::mutableSetOf) += Trace(methodTrace)
                }
                is MethodCall -> { /* do nothing */ }
                is MethodAction -> unreachable { log.error("Unknown method action: $action") }
                else -> {
                    traceStack.peek() += action
                }
            }
        }
        assert(methodStack.size == traceStack.size) {
            log.error("Unexpected trace: number of method does not correspond to number of trace actions")
        }

        while (methodStack.isNotEmpty()) {
            val m = methodStack.pop()
            methodInfos.getOrPut(m, ::mutableSetOf) += Trace(traceStack.pop())
        }
        countIncrease(methods)
    }

    override fun isCovered(method: Method, bb: BasicBlock): Boolean =
        methodInfos[method]?.any { it.isCovered(bb) } ?: false

    fun Method.isInteresting() = when {
        this.isAbstract -> false
        this.isStaticInitializer -> false
        this.`class`.isSynthetic -> false
        this.isSynthetic -> false
        !this.hasBody -> false
        else -> true
    }

    /**
     * inits our recomputing
     */
    private fun setAlrCovered(methods: MutableList<Method>) {
        val statistics = Statistics.invoke()
        for(m in methods.filter { it in statistics.getMethods() }) {
            val tempBlocks = m.bodyBlocks.filterNot { it.isUnreachable }.map { it.originalBlock }.toMutableSet()
            tempBlocks.addAll(m.catchBlocks.filterNot { it.isUnreachable }.map { it.originalBlock })
            alrCoveredBlocks.addAll(tempBlocks.filter{ this.isCovered(m, it) })

            val tempBranches = mutableSetOf<BasicBlock>()
            for (block in tempBlocks.toSet())
                if(block.terminator is BranchInst || block.terminator is SwitchInst || block.terminator is TableSwitchInst)
                    tempBranches.addAll(block.successors)
            alrCoveredBranches.addAll(tempBranches.filter{ this.isCovered(m, it) })

        }
        coveredBlocksCnt = alrCoveredBlocks.toSet().size
        coveredBranchesCnt = alrCoveredBranches.toSet().size
    }

    private fun countIncrease(methods: MutableList<Method>) {
        val statistics = Statistics.invoke()

        val newlyCoveredBlocks = mutableSetOf<BasicBlock>()
        val newlyCoveredBranches = mutableSetOf<BasicBlock>()

        for(m in methods.filter { it in statistics.getMethods() }) {
            val tempBlocks = m.bodyBlocks.filterNot { it.isUnreachable }.map { it.originalBlock }.toMutableSet()
            tempBlocks.addAll(m.catchBlocks.filterNot { it.isUnreachable }.map { it.originalBlock })
            newlyCoveredBlocks.addAll(tempBlocks.filter { this.isCovered(m, it) && !alrCoveredBlocks.contains(it) })

            val tempBranches = mutableSetOf<BasicBlock>()
            for (block in tempBlocks.toSet())
                if(block.terminator is BranchInst || block.terminator is SwitchInst || block.terminator is TableSwitchInst)
                    tempBranches.addAll(block.successors)
            newlyCoveredBranches.addAll(tempBranches.filter { this.isCovered(m, it) && !alrCoveredBranches.contains(it) })
        }

        Statistics.invoke().computeCoveragePercentage(newlyCoveredBlocks.toSet().size, newlyCoveredBranches.toSet().size)
    }

}

