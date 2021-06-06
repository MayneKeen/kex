package org.jetbrains.research.kex.asm.analysis.concolic

import org.jetbrains.research.kex.asm.manager.isUnreachable
import org.jetbrains.research.kex.asm.manager.originalBlock
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.BranchInst
import org.jetbrains.research.kfg.ir.value.instruction.SwitchInst
import org.jetbrains.research.kfg.ir.value.instruction.TableSwitchInst
import org.jetbrains.research.kthelper.logging.log
import java.io.File
import java.io.IOException
import java.nio.file.Files
import java.nio.file.StandardOpenOption
import java.time.Duration
import java.time.temporal.ChronoUnit

class Statistics private constructor() {

    fun incrementSolverRequests() {
        solverRequests++
    }
    fun incrementSatResults() {
        satResults++
    }

    fun startIterationTimeMeasurement() {
        currentItStart = System.currentTimeMillis()
    }

    fun stopBranchSelectionMeasurement() {
        branchSelDurations += Duration.of(System.currentTimeMillis() - currentItStart, ChronoUnit.MILLIS)
    }

    //an iteration is failed if we havent process any trace /and got emptyTrace or null from execute() method
    fun stopIterationTimeMeasurement(fail: Boolean) {
        itDurations += Duration.of(System.currentTimeMillis() - currentItStart, ChronoUnit.MILLIS)
        if(fail)
            failedIterations += iteration

        computeCoverageIncrease(fail)

        iteration++
    }

    fun measureOverallTime() {
        elapsedTime = System.currentTimeMillis()
    }

    fun stopTimeMeasurement(/*fail: Boolean*/) {
        elapsedTime = System.currentTimeMillis() - elapsedTime
    }
    /**
    input: new bodyBlocks+catchBlocks, branches+catchBranches COUNTS covered
    //////call in traceManager//////
    computes !every! trace stats
    not chained to algorithm iterations
     */
/*    fun computeCoveragePercentage(block: Int, branch: Int*//*, fail: Boolean*//*) {
        coveredBlocks += block
        coveredBranches += branch

        val body = coveredBlocks.toDouble() / bodyBlocks
        val br = coveredBranches.toDouble() / branches
        addCoveragePercentage(body, br)
    }
    private fun addCoveragePercentage(body: Double, branch: Double) {
        bodyCoveragePercentage += body * 100
        branchCoveragePercentage += branch * 100
    }
    */
    fun computeCoveragePercentage(block: Int, branch: Int/*, fail: Boolean*/) {
        coveredBlocks += block
        coveredBranches += branch

        val blockPercentage = coveredBlocks.toDouble() / bodyBlocks
        val branchPercentage = coveredBranches.toDouble() / branches

        increaseCurrentCoverage(block, branch)

        addCoveragePercentage(blockPercentage, branchPercentage)

    }

    private fun addCoveragePercentage(body: Double, branch: Double) {
        bodyCoveragePercentage.add(body)
        branchCoveragePercentage.add(branch)
    }

    private fun increaseCurrentCoverage(block: Int, branch: Int) {
        currBodyIncr += block
        currBranchIncr += branch
    }

    //should be called only after successful algorithm iteration -- it has processed a trace, no matter what
    //chained to iterations
    //adds -noChanges- if fail

    fun computeCoverageIncrease(fail: Boolean) {
        if(fail) {
            /*addCoverageIncrease(currBodyIncr.toDouble() / bodyBlocks,
                currBranchIncr.toDouble() / branches)*/

            addCoverageIncrease(0.toDouble(), 0.toDouble())
            currBodyIncr = 0
            currBranchIncr = 0
            return
        }

        addCoverageIncrease(currBodyIncr.toDouble() / bodyBlocks,
            currBranchIncr.toDouble() / branches)
        currBodyIncr = 0
        currBranchIncr = 0
        return
    }


    private fun addCoverageIncrease(body: Double, branch: Double) {
        bodyCoverageIncrease += body
        branchCoverageIncrease += branch
    }

    fun addUnreachable(blocks: Int, branches: Int, method: Method) {
        if(method in getMethods()) {
            unreachableBlocks += blocks
            unreachableBranches += branches
        }
    }

    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    //printing

    //overall
    fun avgIterationTime(): Long = itDurations.map{ it.toMillis() }.sum() / itDurations.size
    //successful
    fun avgSuccessfulIterationTime(): Long {
        val succeed = itDurations.filter { itDurations.indexOf(it) !in failedIterations }.map{ it.toMillis() }
        return succeed.sum() / succeed.size
    }

    fun avgBranchSelectionTime(): Long {
        val successful = branchSelDurations.filter {
            branchSelDurations.indexOf(it) !in failedIterations }.map{ it.toMillis() }
        if(successful.isEmpty())
            return 0.toLong()
        return successful.sum() / successful.size
    }

    private fun avgCoverageIncrease(): String {
        val avgBody = bodyCoverageIncrease.sum() / bodyCoverageIncrease.size
        val avgBranch = branchCoverageIncrease.sum() / branchCoverageIncrease.size
        val successBodyList = bodyCoverageIncrease.filterNot { bodyCoverageIncrease.indexOf(it) in failedIterations}
        val successBranchList = branchCoverageIncrease.filterNot { branchCoverageIncrease.indexOf(it) in failedIterations}
        val avgSuccessBody = successBodyList.sum()  / successBodyList.size
        val avgSuccessBranch = successBranchList.sum()  / successBranchList.size

        val sb = StringBuilder()
        sb.append("     average body coverage increase = ${avgBody * 100}\n")
        sb.append("     average branch coverage increase = ${avgBranch * 100}\n")
        sb.append("     average body coverage increase (successful iterations) = ${avgSuccessBody * 100}\n")
        sb.append("     average branch coverage increase (successful iterations) = ${avgSuccessBranch * 100}\n")
        return sb.toString()
    }

    private fun totalCoverage(): String {
        val body = bodyCoveragePercentage.last()*100
        val branch = branchCoveragePercentage.last()*100
        return "    full = $body    \nbranch = $branch"
    }

    override fun toString(): String {
        val sb = StringBuilder()
        sb.append("Overall statistics:")
        sb.append("\n")
        sb.append(" elapsed time = $elapsedTime")
        sb.append("\n")
        sb.append(" number of iterations = $iteration")
        sb.append("\n")
        sb.append(" number of failed iterations = ${failedIterations.size}")
        sb.append("\n")
        sb.append(" total coverage :\n ${totalCoverage()}")
        sb.append("\n")
        sb.append(" total solver requests = $solverRequests")
        sb.append("\n")
        sb.append(" sat results = $satResults")
        sb.append("\n")
        sb.append(" avg iteration time = ${avgIterationTime()}")
        sb.append("\n")
        sb.append(" avg successful iteration time = ${avgSuccessfulIterationTime()}")
        sb.append("\n")
        sb.append(" avg branch selection time = ${avgBranchSelectionTime()}")
        sb.append("\n")
        sb.append(" coverage increase : ${avgCoverageIncrease()}")
        sb.append("\n")

        sb.append(" covered branches: $coveredBranches || total : $branches \n")
        sb.append("     unreachable : $unreachableBranches\n")

        sb.append(" covered blocks: $coveredBlocks || total : $bodyBlocks\n")
        sb.append("     unreachable : $unreachableBlocks\n")

        sb.append(" body coverage: $bodyCoveragePercentage%\n")
        sb.append("     unreachable percentage : ${(unreachableBlocks*100).toDouble() / bodyBlocks}%\n")
        sb.append(" branch coverage: $branchCoveragePercentage%\n")
        sb.append("     unreachable percentage : ${(unreachableBranches*100).toDouble() / branches}%\n")

        sb.append(" body coverage inc : $bodyCoverageIncrease\n")
        sb.append(" branch coverage inc : $branchCoverageIncrease\n")

        return sb.toString()
    }

    fun print() {
        log.debug(this.toString())
    }

    fun log() {
        val str = this.toString()
        if (logFile != null) {
            try {
                val writer = Files.newBufferedWriter(logFile!!.toPath(), StandardOpenOption.APPEND)
                //writer.newLine()
                writer.write(str)
                writer.newLine()
                writer.flush()
                writer.close()
            }
            catch (e: IOException) {
                log.warn("IOException $e occurred while writing statistics to log file.")
            }
        }
        log.debug(str)
    }

    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    //init

    fun start(file: File, createNew: Boolean, alg: String, pkg: Package, cm: ClassManager) {
        setAlg(alg)
        setPkg(pkg)
        setLoggingFile(file, createNew)
        initCoverageParams(cm)
    }

    private fun initCoverageParams(cm: ClassManager) {
        classManager = cm
        val allMethods = mutableSetOf<Method>()

        fun Method.isInteresting() = when {
            this.isAbstract -> false
            this.isStaticInitializer -> false
            this.`class`.isSynthetic -> false
            this.isSynthetic -> false
            !this.hasBody -> false
            else -> true
        }
        cm.concreteClasses.filter { target!!.isParent(it.`package`) }.forEach {
            allMethods.addAll(it.allMethods)
        }

        methods = allMethods.filter { it.isInteresting() }.toMutableSet()

        val blockSet = mutableSetOf<BasicBlock>()
        for (m in methods) {
            blockSet.addAll(m.bodyBlocks.filterNot { it.isUnreachable }.map { it.originalBlock })
            blockSet.addAll(m.catchBlocks.filterNot { it.isUnreachable }.map { it.originalBlock })
        }

        val branchSet = mutableSetOf<BasicBlock>()
        blockSet.toSet().forEach{ if(it.terminator is BranchInst || it.terminator is SwitchInst || it.terminator is TableSwitchInst)
            branchSet.addAll(it.successors) }

        allBlocks = blockSet

        bodyBlocks = blockSet.toSet().size
        branches = branchSet.toSet().size
        return
    }

    private fun setLoggingFile(file: File, createNew: Boolean) {
        logFile = file
        if (createNew) {
            var i = 1
            var newFile = File(file.path + "$i.log")
            while(newFile.exists()) {
                newFile = File(file.path + "$i.log")
                i++
            }
            newFile.parentFile.mkdirs()
            newFile.createNewFile()
            log.info("Stats will be here: " + newFile.path.toString())

            val writer = Files.newBufferedWriter(newFile.toPath(), StandardOpenOption.WRITE)
            writer.write("algorithm: ${algorithm}, target: ${target?.name}")
            writer.newLine()
            writer.flush()
            writer.close()
            logFile = newFile
        }
    }

    private fun setAlg(alg: String) {
        algorithm = alg
    }

    private fun setPkg(pkg: Package) {
        target = pkg
    }


    companion object {
        private var instance: Statistics? = null
        operator fun invoke(): Statistics = synchronized(this) {
            if (instance == null)
                instance = Statistics()
            instance!!
        }
        var methods = mutableSetOf<Method>()
        var allBlocks = mutableSetOf<BasicBlock>()
        var classManager: ClassManager? = null
        var elapsedTime = 0.toLong()
        var bodyBlocks = 0
        var branches = 0
        var coveredBlocks = 0
        var coveredBranches = 0
        var unreachableBlocks = 0
        var unreachableBranches = 0

        var iteration = 0
        var currentItStart = 0.toLong()


        val bodyCoveragePercentage = mutableListOf(0.toDouble())
        val branchCoveragePercentage = mutableListOf(0.toDouble())
        val bodyCoverageIncrease = mutableListOf<Double>()            //chained to iteration numbers ++ add -nochanges- if fail
        val branchCoverageIncrease = mutableListOf<Double>()

        val failedIterations = mutableListOf<Int>()
        val itDurations = mutableListOf<Duration>()
        val branchSelDurations = mutableListOf<Duration>()
        var solverRequests = 0
        var satResults = 0

        var currBodyIncr = 0
        var currBranchIncr = 0



        var algorithm = ""
        var target: Package? = null
        var logFile: File? = null
    }

    fun getCM() = classManager
    fun getTarget() = target

    fun inBlocks(bb: BasicBlock) = bb in allBlocks

    fun getMethods() = methods.toSet()
}
