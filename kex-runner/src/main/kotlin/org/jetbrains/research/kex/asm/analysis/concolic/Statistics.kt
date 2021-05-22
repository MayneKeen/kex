package org.jetbrains.research.kex.asm.analysis.concolic

import org.jetbrains.research.kthelper.logging.log
import java.time.Duration
import java.time.temporal.ChronoUnit
import java.util.zip.DeflaterOutputStream
import kotlin.reflect.jvm.internal.impl.resolve.scopes.StaticScopeForKotlinEnum
import kotlin.system.exitProcess

class Statistics private constructor() {

    var algorithm = ""

    private fun Statistics.getMethodStats(/*algorithm: String,*/ methodName: String): MethodStats {
        var ms = methodHolder.find { it.methodName == methodName /*&& it.algorithm == algorithm */}
        return if (ms != null)
            ms
        else {
            ms = MethodStats(/*algorithm,*/ methodName)
            methodHolder += ms
            ms
        }
    }
//
//    fun setAlg(algorithm: String) {
//        this.algorithm = algorithm
//    }

    /**
     * Starts measuring one iteration time + iterations number  **/

    fun startIterationTimeMeasurement(methodName: String/*, algorithm: String*/) {
        val ms = this.getMethodStats(methodName/*, algorithm*/)
        ms.iterationsStart += System.currentTimeMillis()
    }

    /**
     * Stops measuring one iteration time + iterations number  **/

    fun stopIterationTimeMeasurement(methodName: String/*, algorithm: String*/) {
        val ms = this.getMethodStats(methodName/*, algorithm*/)

        try {
            val itStart = ms.iterationsStart[ms.itNumber-1]
            ms.itDurations += Duration.of(System.currentTimeMillis() - itStart, ChronoUnit.MILLIS)
        } catch (e: ArrayIndexOutOfBoundsException) {
            log.debug(
                "Statistics: an $e occurred while measuring iteration #${ms.itNumber} time," +
                        " in $methodName Duration.ZERO recorded"
            )
            ms.itDurations += Duration.ZERO
        }
        ms.itNumber++
        return
    }

    /**
     * Measuring branch selection time **/

    fun stopBranchSelectionMeasurement(methodName: String/*, algorithm: String*/) {
        val ms = this.getMethodStats(methodName/*, algorithm*/)

        try {
            val itStart = ms.iterationsStart[ms.itNumber-1]
            ms.branchSelectionDuration.add(Duration.of(
                System.currentTimeMillis() - itStart, ChronoUnit.MILLIS))
        } catch (e: ArrayIndexOutOfBoundsException) {
            log.debug(
                "Statistics: an $e occurred while measuring iteration #${ms.itNumber} time," +
                        " in $methodName. Duration.ZERO recorded")
            ms.branchSelectionDuration.add(Duration.ZERO)
        }
        return
    }

    /**
     * Starts measuring elapsed time  **/
    fun measureOverallTime(methodName: String/*, algorithm: String*/) {
        this.getMethodStats(methodName/*, algorithm*/).startTime = System.currentTimeMillis()
    }

    /**
     * If fail==false: Stops measurement of elapsed time.
     * Else: Stops all measurements**/

    fun stopTimeMeasurement(methodName: String, fail: Boolean/*, algorithm: String*/) {
        if(fail) {
            stopBranchSelectionMeasurement(methodName)
            stopIterationTimeMeasurement(methodName)
        }
        val ms = getMethodStats(methodName/*, algorithm*/)
        ms.elapsedTime = Duration.of(System.currentTimeMillis() - ms.startTime, ChronoUnit.MILLIS)
    }

    /**
     * Incrementing number of solver requests  **/

    fun incrementSolverRequests(methodName: String/*, algorithm: String*/) {
        getMethodStats(methodName/*, algorithm*/).solverCalls++
    }

    /**
     * Setting total coverage + total branch coverage  **/

    fun updateMethodCoverage(methodName: String) {
        val ms = getMethodStats(methodName/*, algorithm*/)
        if(ms.isEmpty())
            return
        ms.bodyFull = ms.fullBodyCoverage.last()
        ms.branchFull = ms.fullBranchCoverage.last()
    }

//    fun setTotalCoverageValues(ms: MethodStats/*, algorithm: String*/, bodyFull: Double, branchFull: Double) {
//        ms.bodyFull = bodyFull
//        ms.branchFull = branchFull
//    }

    /**
     * Measuring average project coverage  **/
    fun countAvgCoverage() {
        var coverage = 0.0
        var branchCoverage = 0.0
        methodHolder.forEach {
            coverage += it.bodyFull
            branchCoverage += it.branchFull
        }

        avgCoverage = coverage / methodHolder.size
        avgBranchCoverage = branchCoverage / methodHolder.size
    }




    /**
     * Collecting dynamic body/full coverage stats **/

    fun addIterationBodyCoverage(methodName: String/*, algorithm: String*/, body: Double, full: Double) {
        val ms = getMethodStats(methodName/*, algorithm*/)
        ms.bodyCoverage.add(body)
        ms.fullBodyCoverage.add(full)
        if(ms.isEmpty() || ms.branchCoverage.isEmpty() || ms.fullBranchCoverage.isEmpty())
            return
        updateMethodCoverage(methodName)
    }

    /**
     * Collecting dynamic branch/branchFull coverage stats **/

    fun addIterationBranchCoverage(methodName: String/*, algorithm: String*/, branch: Double, branchFull: Double) {
        val ms = getMethodStats(methodName/*, algorithm*/)
        ms.branchCoverage.add(branch)
        ms.fullBranchCoverage.add(branchFull)
        if(ms.isEmpty() || ms.branchCoverage.isEmpty() || ms.fullBranchCoverage.isEmpty())
            return
        updateMethodCoverage(methodName)
    }

    /**
     * Printing Statistics**/
    fun print(){
        var iterations = 0
        var elapsedTime = 0.toLong()
        var bodyCoverage = 0.toDouble()
        var branchCoverage = 0.toDouble()
        var calls = 0
        var branchSelection = 0.toLong()

        methodHolder.forEach{
            iterations += it.itNumber
            elapsedTime += it.elapsedTime.toMillis()
            bodyCoverage += it.bodyFull
            branchCoverage += it.branchFull
            calls += it.solverCalls
            branchSelection += it.avgBranchSelectionTime()
        }

        bodyCoverage /= methodHolder.size
        branchCoverage /= methodHolder.size
        branchSelection /= methodHolder.size


        val sb = StringBuilder()
        sb.append("Overall statistics: \n")
        sb.append("     number of iterations: ${iterations}\n")
        sb.append("     elapsed time: ${elapsedTime}\n")
        sb.append("     full body coverage: ${bodyCoverage/methodHolder.size}\n")
        sb.append("     full branch coverage: ${branchCoverage/methodHolder.size}\n")
        sb.append("     total solver calls: ${calls}\n")
        sb.append("     average branch selection time millis: ${branchSelection/methodHolder.size}\n")
        println(sb.toString())


    }


    /**
     * Printing Statistics**/
    fun print(methodName: String) {
        val ms = getMethodStats(methodName)
        if(ms.isEmpty()){
            println("Statistics: no results for method $methodName")
            return
        }
        val sb = StringBuilder()
        sb.append("Method $methodName statistics: \n")
        sb.append("     number of iterations: ${ms.itNumber}\n")
        sb.append("     elapsed time: ${ms.elapsedTime.toMillis()}\n")
        sb.append("     full body coverage: ${ms.bodyFull}\n")
        sb.append("     full branch coverage: ${ms.branchFull}\n")
        sb.append("     total solver calls: ${ms.solverCalls}\n")
        sb.append("     average branch selection time millis: ${ms.avgBranchSelectionTime()}\n")
        println(sb.toString())

    }


    fun MethodStats.avgBranchSelectionTime(): Long {
        if(this.branchSelectionDuration.isEmpty())
            return 0.0.toLong()
        var sum = 0.0.toLong()
        this.branchSelectionDuration.forEach{ sum += it.toMillis() }
        return sum / this.branchSelectionDuration.size
    }

    companion object {
        private var instance: Statistics? = null
        operator fun invoke(): Statistics = synchronized(this) {
            if (instance == null)
                instance = Statistics()
//            instance?.setAlg()
            instance!!
        }

        val methodHolder = mutableSetOf<MethodStats>()
        var avgCoverage = 0.0
        var avgBranchCoverage = 0.0

    }

}

data class MethodStats(//val algorithm: String,
                       val methodName: String
                       ) {
    //number of current iteration
    //after execution here we should have total amount of iterations
    var itNumber = 1

    //start in milliseconds for each iteration while testing the method
    val iterationsStart = mutableListOf<Long>()
    //start in milliseconds for each iteration while testing the method
    val itDurations = mutableListOf<Duration>()


    //method analysis start time
    var startTime = 0.toLong()
    //method analysis end time
    var elapsedTime = Duration.ZERO!!

    //total method coverage
//    var totalCoverage = 0.0
//    var totalBranchCoverage = 0.0

    var bodyFull = 0.0
    var branchFull = 0.0

    var solverCalls = 0
    var branchSelectionDuration = mutableListOf<Duration>()

    val bodyCoverage = mutableListOf<Double>()
    val branchCoverage = mutableListOf<Double>()

    val fullBodyCoverage = mutableListOf<Double>()
    val fullBranchCoverage = mutableListOf<Double>()


    fun isEmpty() = itNumber == 1 && bodyCoverage.isEmpty() && branchCoverage.isEmpty() &&
            fullBodyCoverage.isEmpty() && fullBranchCoverage.isEmpty()

    fun isNotEmpty() = !this.isEmpty()

    override fun hashCode() = super.hashCode() /*+ algorithm.hashCode()*/ + methodName.hashCode() + startTime.hashCode()

    override fun toString(): String {
        return super.toString()
    }
    override fun equals(other: Any?) =
        if(other is MethodStats)
            /*this.algorithm == other.algorithm &&*/ this.methodName == other.methodName && super.equals(other)
//                    &&
//                    this.itNumber == other.itNumber && this.itDurations == other.itDurations &&
//                    this.startTime == other.startTime && this.elapsedTime == other.elapsedTime &&
//                    this.totalCoverage == other.totalCoverage && this.totalBranchCoverage == other.totalBranchCoverage &&
//                    this. branchSelectionDuration == other.branchSelectionDuration && this.solverCalls == other.solverCalls
        else false


}