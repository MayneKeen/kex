package org.jetbrains.research.kex.asm.analysis.concolic

import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kthelper.logging.log
import java.io.File
import java.io.IOException
import java.nio.file.Files
import java.nio.file.StandardOpenOption
import java.time.Duration
import java.time.temporal.ChronoUnit
import kotlin.system.exitProcess

class Statistics private constructor() {

    private fun Statistics.getMethodStats(/*algorithm: String,*/ method: Method): MethodStats {
        var ms = methodHolder.find { it.method == method /*&& it.algorithm == algorithm */ }
        return if (ms != null)
            ms
        else {
            ms = MethodStats(/*algorithm,*/ method)
            methodHolder += ms
            ms
        }
    }

    /**
     * Starts measuring one iteration time + iterations number  **/

    fun startIterationTimeMeasurement(method: Method/*, algorithm: String*/) {
        val ms = getMethodStats(method/*, algorithm*/)
        ms.iterationsStart += System.currentTimeMillis()
    }

    /**
     * Stops measuring one iteration time + iterations number  **/

    fun stopIterationTimeMeasurement(method: Method/*, algorithm: String*/) {
        val ms = getMethodStats(method/*, algorithm*/)

        try {
            val itStart = ms.iterationsStart[ms.itNumber]
            ms.itDurations += Duration.of(System.currentTimeMillis() - itStart, ChronoUnit.MILLIS)
        } catch (e: ArrayIndexOutOfBoundsException) {
            log.debug(
                "Statistics: an $e occurred while measuring iteration #${ms.itNumber} time," +
                        " in ${method.name} Duration.ZERO recorded"
            )
            ms.itDurations += Duration.ZERO
        }
        ms.itNumber++
        return
    }

    /**
     * Measuring branch selection time **/

    fun stopBranchSelectionMeasurement(method: Method/*, algorithm: String*/) {
        val ms = getMethodStats(method/*, algorithm*/)

        try {
            val itStart = ms.iterationsStart[ms.itNumber]
            ms.branchSelectionDuration.add(
                Duration.of(
                    System.currentTimeMillis() - itStart, ChronoUnit.MILLIS
                )
            )
        } catch (e: ArrayIndexOutOfBoundsException) {
            log.debug(
                "Statistics: an $e occurred while measuring iteration #${ms.itNumber} time," +
                        " in ${method.name}. Duration.ZERO recorded"
            )
            ms.branchSelectionDuration.add(Duration.ZERO)
        }
        return
    }

    /**
     * Starts measuring elapsed time  **/
    fun measureOverallTime(method: Method/*, algorithm: String*/) {
        getMethodStats(method/*, algorithm*/).startTime = System.currentTimeMillis()
    }

    /**
     * If fail==false: Stops measurement of elapsed time.
     * Else: Stops all measurements**/

    fun stopTimeMeasurement(method: Method, fail: Boolean/*, algorithm: String*/) {
        if (fail) {
            stopBranchSelectionMeasurement(method)
            stopIterationTimeMeasurement(method)
        }
        val ms = getMethodStats(method/*, algorithm*/)
        ms.elapsedTime = Duration.of(System.currentTimeMillis() - ms.startTime, ChronoUnit.MILLIS)
    }

    /**
     * Incrementing number of solver requests  **/

    fun incrementSolverRequests(method: Method/*, algorithm: String*/) {
        getMethodStats(method/*, algorithm*/).solverCalls++
    }

    /**
     * Setting total coverage + total branch coverage  **/

    fun updateMethodCoverage(method: Method) {
        val ms = getMethodStats(method/*, algorithm*/)
        if (ms.isEmpty())
            return
        ms.bodyFull = ms.fullBodyCoverage.last()
        ms.branchFull = ms.fullBranchCoverage.last()
    }

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

    fun addIterationBodyCoverage(method: Method/*, algorithm: String*/, body: Double, full: Double) {
        val ms = getMethodStats(method/*, algorithm*/)
        ms.bodyCoverage.add(body)
        ms.fullBodyCoverage.add(full)
        if (ms.isEmpty() || ms.branchCoverage.isEmpty() || ms.fullBranchCoverage.isEmpty())
            return
        updateMethodCoverage(method)
    }

    /**
     * Collecting dynamic branch/branchFull coverage stats **/

    fun addIterationBranchCoverage(method: Method/*, algorithm: String*/, branch: Double, branchFull: Double) {
        val ms = getMethodStats(method/*, algorithm*/)
        ms.branchCoverage.add(branch)
        ms.fullBranchCoverage.add(branchFull)
        if (ms.isEmpty() || ms.branchCoverage.isEmpty() || ms.fullBranchCoverage.isEmpty())
            return
        updateMethodCoverage(method)
    }

    private fun MethodStats.avgBranchSelectionTime(): Long {
        if (this.branchSelectionDuration.isEmpty())
            return 0.0.toLong()
        var sum = 0.0.toLong()
        this.branchSelectionDuration.forEach { sum += it.toMillis() }
        return sum / this.branchSelectionDuration.size
    }

    fun setOtherMethodCoverage(
        method: Method, other: Method, body: Double, bodyFull: Double,
        branch: Double, branchFull: Double
    ) {
        if (method == other) {
            log.error(
                "Statistics: setting other method coverage for method: ${method.name} " +
                        "failed because other method is the same"
            )
            return
        }

        val ms = getMethodStats(method)
        var otm = ms.otherMethodsInfo[other]
        val notSet = otm == null
        if (notSet)
            otm = OtherMethodInfo(method, other)

        otm!!.bodyCoverage.add(body)
        otm.fullBodyCoverage.add(bodyFull)
        otm.branchCoverage.add(branch)
        otm.fullBranchCoverage.add(branchFull)
        otm.itNumber++

        if (notSet)
            ms.otherMethodsInfo[other] = otm
        return
    }

    /**
     * Printing Statistics**/
    fun print() {
        println(this.toString())
        return
    }

    /**
     * Printing Statistics by method**/
    fun print(method: Method) {
        val str = getStatsString(method)
        println(str)
        return
    }

    fun log() {
        if (logFile != null) {
            try {
                val writer = Files.newBufferedWriter(logFile!!.toPath(), StandardOpenOption.APPEND)
                writer.write(this.toString())
                writer.newLine()
                writer.flush()
                writer.close()
            } catch (e: IOException) {
                log.warn("IOException $e occurred while writing statistics to log file.")
            }
        } else {
            log.debug(this.toString())
        }
    }

    override fun toString(): String {
        var iterations = 0
        var elapsedTime = 0.toLong()
        var bodyCoverage = 0.toDouble()
        var branchCoverage = 0.toDouble()
        var calls = 0
        var branchSelection = 0.toLong()

        methodHolder.forEach {
            iterations += it.itNumber
            elapsedTime += it.elapsedTime.toMillis()
            bodyCoverage += it.bodyFull
            branchCoverage += it.branchFull
            calls += it.solverCalls
            branchSelection += it.avgBranchSelectionTime()
        }
        val sb = StringBuilder()
        sb.append("Overall statistics: \n")
        sb.append("     number of methods: ${methodHolder.size}\n")
        sb.append("     number of iterations: ${iterations}\n")
        sb.append("     elapsed time: ${elapsedTime} ms\n")
        sb.append("     avg body coverage: ${bodyCoverage / methodHolder.size}\n")
        sb.append("     avg branch coverage: ${branchCoverage / methodHolder.size}\n")
        sb.append("     total solver calls: ${calls}\n")
        sb.append("     avg branch selection time: ${branchSelection / methodHolder.size} ms\n")
        return sb.toString()
    }

    private fun getStatsString(method: Method): String {
        val ms = getMethodStats(method)
        if (ms.isEmpty()) {
            return "Statistics: no results for method ${method.name}"
        }

        val listMethods = mutableListOf<String>()
        for (m in ms.otherMethodsInfo.keys)
            listMethods.add(m.name + " coverage is: ${ms.otherMethodsInfo[m].toString()} \n")

        val sb = StringBuilder()
        sb.append("Method ${method.name} statistics: \n")
        sb.append("     number of iterations: ${ms.itNumber}\n")
        sb.append("     elapsed time: ${ms.elapsedTime.toMillis()}\n")
        sb.append("     full body coverage: ${ms.bodyFull}\n")
        sb.append("     full branch coverage: ${ms.branchFull}\n")
        sb.append("     total solver calls: ${ms.solverCalls}\n")
        sb.append("     average branch selection time millis: ${ms.avgBranchSelectionTime()}\n")
        sb.append("     following methods were called: ${listMethods.toString()}")
        return sb.toString()
    }

    companion object {
        private var instance: Statistics? = null
        operator fun invoke(): Statistics = synchronized(this) {
            if (instance == null)
                instance = Statistics()
            instance!!
        }

        val methodHolder = mutableSetOf<MethodStats>()
        var avgCoverage = 0.0
        var avgBranchCoverage = 0.0

        fun setLoggingFile(file: File, createNew: Boolean) {
            logFile = file
            if (createNew) {
                if (file.exists()) {
                    file.delete()
                }
                file.createNewFile()
                val writer = Files.newBufferedWriter(file.toPath(), StandardOpenOption.WRITE)
                writer.write("algorithm: $algorithm")
                writer.newLine()
                writer.flush()
                writer.close()
            }
        }

        fun setAlg(algorithm: String) {
            this.algorithm = algorithm
        }

        var algorithm = ""
            private set
        var logFile: File? = null
            private set
    }

}

data class OtherMethodInfo(
    val method: Method,
    val other: Method
) {
    var itNumber = 0

    val bodyCoverage = mutableListOf<Double>()
    val branchCoverage = mutableListOf<Double>()

    val fullBodyCoverage = mutableListOf<Double>()
    val fullBranchCoverage = mutableListOf<Double>()

    override fun equals(other: Any?): Boolean {
        return if (other is OtherMethodInfo)
            this.method == other.method && this.other == other.other && this.itNumber == other.itNumber &&
                    this.bodyCoverage == other.bodyCoverage && this.branchCoverage == other.branchCoverage &&
                    this.fullBodyCoverage == other.fullBodyCoverage && this.fullBranchCoverage == other.fullBranchCoverage
        else false
    }

    override fun hashCode(): Int {
        return super.hashCode() + method.hashCode() + other.hashCode()
    }

    override fun toString(): String {
        val sb = StringBuilder()
        if (fullBodyCoverage.isNotEmpty())
            sb.append("\n       body " + fullBodyCoverage.last() + "\n")
        if (fullBranchCoverage.isNotEmpty())
            sb.append("       branch: " + fullBranchCoverage.last() + "\n")
        return sb.toString()
    }
}

data class MethodStats(//val algorithm: String,
    val method: Method
) {
    //number of current iteration
    //after execution here we should have total amount of iterations
    var itNumber = 0

    //start in milliseconds for each iteration while testing the method
    val iterationsStart = mutableListOf<Long>()

    //start in milliseconds for each iteration while testing the method
    val itDurations = mutableListOf<Duration>()


    //method analysis start time
    var startTime = 0.toLong()

    //method analysis end time
    var elapsedTime = Duration.ZERO!!

    //avg method coverage
    var bodyFull = 0.0
    var branchFull = 0.0

    var solverCalls = 0
    var branchSelectionDuration = mutableListOf<Duration>()

    val bodyCoverage = mutableListOf<Double>()
    val branchCoverage = mutableListOf<Double>()

    val fullBodyCoverage = mutableListOf<Double>()
    val fullBranchCoverage = mutableListOf<Double>()

    //otherMethod :: info
    val otherMethodsInfo = mutableMapOf<Method, OtherMethodInfo>()


    fun isEmpty() = itNumber == 0 && bodyCoverage.isEmpty() && branchCoverage.isEmpty() &&
            fullBodyCoverage.isEmpty() && fullBranchCoverage.isEmpty() && solverCalls == 0 && otherMethodsInfo.isEmpty()

    fun isNotEmpty() = !this.isEmpty()

    override fun hashCode() = super.hashCode() /*+ algorithm.hashCode()*/ + method.hashCode() + startTime.hashCode()

    override fun toString(): String {
        return super.toString()
    }

    override fun equals(other: Any?) =
        if (other is MethodStats)
        /*this.algorithm == other.algorithm &&*/ this.method == other.method && super.equals(other)
//                    &&
//                    this.itNumber == other.itNumber && this.itDurations == other.itDurations &&
//                    this.startTime == other.startTime && this.elapsedTime == other.elapsedTime &&
//                    this.totalCoverage == other.totalCoverage && this.totalBranchCoverage == other.totalBranchCoverage &&
//                    this. branchSelectionDuration == other.branchSelectionDuration && this.solverCalls == other.solverCalls
        else false


}