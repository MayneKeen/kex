package org.jetbrains.research.kex.trace.`object`

import org.jetbrains.research.kex.asm.analysis.concolic.Statistics
import org.jetbrains.research.kex.asm.manager.CoverageInfo
import org.jetbrains.research.kex.asm.manager.isUnreachable
import org.jetbrains.research.kex.asm.manager.originalBlock
import org.jetbrains.research.kthelper.assert.unreachable
import org.jetbrains.research.kthelper.collection.stackOf
import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.trace.TraceManager
import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.BranchInst
import org.jetbrains.research.kfg.ir.value.instruction.SwitchInst
import org.jetbrains.research.kfg.ir.value.instruction.TableSwitchInst

class ObjectTraceManager : TraceManager<Trace> {
    private val methodInfos = mutableMapOf<Method, MutableSet<Trace>>()
    private val fullTraces = mutableSetOf<Trace>()

    override fun getTraces(method: Method): List<Trace> = methodInfos.getOrDefault(method, mutableSetOf()).toList()

    override fun addTrace(method: Method, trace: Trace) {
        fullTraces += trace
        val traceStack = stackOf<MutableList<Action>>()
        val methodStack = stackOf<Method>()
        val methods = mutableListOf<Method>()

        for (action in trace) {
            when (action) {
                is MethodEntry -> {
                    traceStack.push(mutableListOf(action))
                    methodStack.push(action.method)
                    methods.add(action.method)
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
        countCoverage(method, this, null)

        for(m in methods)
            if(m != method)
                countCoverage(m, this, method)
            else continue

    }

    override fun isCovered(method: Method, bb: BasicBlock): Boolean =
        methodInfos[method]?.any { it.isCovered(bb) } ?: false

    private fun countCoverage(m: Method, tm: TraceManager<Trace>, source: Method?) {
        val bodyBlocks = m.bodyBlocks.filterNot { it.isUnreachable }.map { it.originalBlock }.toSet()
        val catchBlocks = m.catchBlocks.filterNot { it.isUnreachable }.map { it.originalBlock }.toSet()
        val bodyCovered = bodyBlocks.count { this.isCovered(m, it) }
        val catchCovered = catchBlocks.count { this.isCovered(m, it) }

        val branches = mutableSetOf<BasicBlock>()
        val catchBranches = mutableSetOf<BasicBlock>()

        for(block in bodyBlocks)
            if(block.terminator is BranchInst || block.terminator is SwitchInst || block.terminator is TableSwitchInst)
                branches.addAll(block.successors)

        for(block in catchBlocks)
            if(block.terminator is BranchInst || block.terminator is SwitchInst || block.terminator is TableSwitchInst)
                catchBranches.addAll(block.successors)

        val branchCovered = branches.count { tm.isCovered(m, it) }
        val catchBranchesCovered = catchBranches.count { tm.isCovered(m, it) }

        val body = (bodyCovered * 100).toDouble() / bodyBlocks.size
        val full = ((bodyCovered + catchCovered) * 100).toDouble() / (bodyBlocks.size + catchBlocks.size)

        var branch = (branchCovered * 100).toDouble() / branches.size
        var branchFull = ((branchCovered + catchBranchesCovered) * 100).toDouble() / (branches.size + catchBranches.size)

        if(branches.size < 1) {
            branch = 100.toDouble()
            if(catchBranches.size < 1)
                branchFull = 100.toDouble()
        }

        val statistics = Statistics.invoke()
        if(source == null) {
            statistics.addIterationBodyCoverage(m, body, full)
            statistics.addIterationBranchCoverage(m, branch, branchFull)
        }
        else {
            statistics.setOtherMethodCoverage(source, m, body, full, branch, branchFull)
        }
    }

}

