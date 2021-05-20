package org.jetbrains.research.kex.asm.manager

import org.jetbrains.research.kex.asm.util.Visibility
import org.jetbrains.research.kex.asm.util.visibility
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.trace.TraceManager
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.BranchInst
import org.jetbrains.research.kfg.ir.value.instruction.SwitchInst
import org.jetbrains.research.kfg.ir.value.instruction.TableSwitchInst
import org.jetbrains.research.kfg.visitor.MethodVisitor
import org.jetbrains.research.kthelper.logging.log
import java.util.*

private val visibilityLevel by lazy { kexConfig.getEnumValue("apiGeneration", "visibility", true, Visibility.PUBLIC) }

val Method.isImpactable: Boolean
    get() = when {
        this.isAbstract -> false
        this.isStaticInitializer -> false
        this.`class`.isSynthetic -> false
        this.isSynthetic -> false
        visibilityLevel > this.`class`.visibility -> false
        visibilityLevel > this.visibility -> false
        else -> true
    }

data class CoverageInfo(val bodyCoverage: Double, val fullCoverage: Double)

class CoverageCounter<T> private constructor(
    override val cm: ClassManager,
    private val tm: TraceManager<T>,
    val methodFilter: (Method) -> Boolean
) : MethodVisitor {
    val methodInfos = hashMapOf<Method, CoverageInfo>()

    constructor(cm: ClassManager, tm: TraceManager<T>) : this(cm, tm, { true })
    constructor(cm: ClassManager, tm: TraceManager<T>, pkg: Package) : this(
        cm,
        tm,
        { pkg.isParent(it.`class`.`package`) })

    constructor(cm: ClassManager, tm: TraceManager<T>, klass: Class) : this(
        cm,
        tm,
        { it.`class` == klass })

    constructor(cm: ClassManager, tm: TraceManager<T>, methods: Set<Method>) : this(
        cm,
        tm,
        { it in methods })

    val totalCoverage: CoverageInfo
        get() {
            if (methodInfos.isEmpty()) return CoverageInfo(0.0, 0.0)

            val numberOfMethods = methodInfos.size
            val (body, full) = methodInfos.values.reduce { acc, coverageInfo ->
                CoverageInfo(
                    acc.bodyCoverage + coverageInfo.bodyCoverage,
                    acc.fullCoverage + coverageInfo.fullCoverage
                )
            }

            return CoverageInfo(body / numberOfMethods, full / numberOfMethods)
        }

    private val Method.isInteresting: Boolean
        get() = when {
            this.isAbstract -> false
            this.isStaticInitializer -> false
            this.`class`.isSynthetic -> false
            this.isSynthetic -> false
            !this.hasBody -> false
            else -> true
        }

    override fun cleanup() {}

    override fun visit(method: Method) {
        if (!method.isInteresting) return
        if (!methodFilter(method)) return

        val bodyBlocks = method.bodyBlocks.filterNot { it.isUnreachable }.map { it.originalBlock }.toSet()
        val catchBlocks = method.catchBlocks.filterNot { it.isUnreachable }.map { it.originalBlock }.toSet()
        val bodyCovered = bodyBlocks.count { tm.isCovered(method, it) }
        val catchCovered = catchBlocks.count { tm.isCovered(method, it) }

        val info = CoverageInfo(
            (bodyCovered * 100).toDouble() / bodyBlocks.size,
            ((bodyCovered + catchCovered) * 100).toDouble() / (bodyBlocks.size + catchBlocks.size)
        )
        methodInfos[method] = info

        log.info(
            "Method $method coverage: " +
                    "body = ${String.format(Locale.ENGLISH, "%.2f", info.bodyCoverage)}; " +
                    "full = ${String.format(Locale.ENGLISH, "%.2f", info.fullCoverage)}"
        )
    }
}

data class BranchCoverageInfo(val branchCoverage: Double, val fullCoverage: Double)

class BranchCoverageCounter<T> private constructor(
    override val cm: ClassManager,
    private val tm: TraceManager<T>,
    val methodFilter: (Method) -> Boolean
    ) : MethodVisitor {

    val methodInfos = hashMapOf<Method, BranchCoverageInfo>()

    constructor(cm: ClassManager, tm: TraceManager<T>) : this(cm, tm, { true })
    constructor(cm: ClassManager, tm: TraceManager<T>, pkg: Package) : this(
        cm,
        tm,
        { pkg.isParent(it.`class`.`package`) })

    constructor(cm: ClassManager, tm: TraceManager<T>, klass: Class) : this(
        cm,
        tm,
        { it.`class` == klass })

    constructor(cm: ClassManager, tm: TraceManager<T>, methods: Set<Method>) : this(
        cm,
        tm,
        { it in methods })


    val totalCoverage: BranchCoverageInfo
        get() {
            if (methodInfos.isEmpty()) return BranchCoverageInfo(0.0, 0.0)

            val numberOfMethods = methodInfos.size
            val (branch, full) = methodInfos.values.reduce { acc, bCoverageInfo ->
                BranchCoverageInfo(
                    acc.branchCoverage + bCoverageInfo.branchCoverage,
                    acc.fullCoverage + bCoverageInfo.fullCoverage,
//                    acc.numberOfBranches + bCoverageInfo.numberOfBranches,
//                    acc.numberCovered + bCoverageInfo.numberCovered
                )
            }

            return BranchCoverageInfo(branch / numberOfMethods, full / numberOfMethods)
//                , number, numberCovered)
        }

    private val Method.isInteresting: Boolean
        get() = when {
            this.isAbstract -> false
            this.isStaticInitializer -> false
            this.`class`.isSynthetic -> false
            this.isSynthetic -> false
            !this.hasBody -> false
            else -> true
        }

    override fun cleanup() {}


    override fun visit(method: Method) {
        if (!method.isInteresting) return
        if (!methodFilter(method)) return

        val bodyBlocks = method.bodyBlocks.filterNot { it.isUnreachable }.map { it.originalBlock }.toSet()
        val catchBlocks = method.catchBlocks.filterNot { it.isUnreachable }.map { it.originalBlock }.toSet()

        val branches = mutableSetOf<BasicBlock>()
        val catchBranches = mutableSetOf<BasicBlock>()

        for(block in bodyBlocks)
            if(block.terminator is BranchInst || block.terminator is SwitchInst || block.terminator is TableSwitchInst)
            branches.addAll(block.successors)

        for(block in catchBlocks)
            if(block.terminator is BranchInst || block.terminator is SwitchInst || block.terminator is TableSwitchInst)
                catchBranches.addAll(block.successors)

        val branchCovered = branches.count { tm.isCovered(method, it) }
        val catchCovered = catchBranches.count { tm.isCovered(method, it) }


        //val branchCoverage: Double, var numberOfBranches, var numberCovered: Int

        val info = BranchCoverageInfo(
            (branchCovered * 100).toDouble() / branches.size,
            ((branchCovered + catchCovered) * 100).toDouble() / (branches.size + catchBranches.size)
        )
        methodInfos[method] = info

        log.info(
            "Method $method coverage: " +
                    "branch = ${String.format(Locale.ENGLISH, "%.2f", info.branchCoverage)}; " +
                    "full = ${String.format(Locale.ENGLISH, "%.2f", info.fullCoverage)}"
        )
    }
}
