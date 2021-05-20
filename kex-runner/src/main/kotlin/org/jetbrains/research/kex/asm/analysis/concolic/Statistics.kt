package org.jetbrains.research.kex.asm.analysis.concolic

import org.jetbrains.research.kthelper.logging.log
import java.time.Duration
import java.time.temporal.ChronoUnit

class Statistics private constructor() {

    private fun Statistics.getMethodStats(algorithm: String, methodName: String): MethodStats {
        var ms = methodHolder.find { it.methodName == methodName && it.algorithm == algorithm }
        return if(ms != null) {
            ms
        } else {
            ms = MethodStats(algorithm, methodName)
            methodHolder += ms
            ms
        }
    }

    /**
     * Measuring one iteration time + iterations number  **/

    fun startIterationTimeMeasurement(methodName: String, algorithm: String) {
        val ms = this.getMethodStats(methodName, algorithm)
        ms.iterationsStart[ms.itNumber] = System.currentTimeMillis()
    }

    fun stopIterationTimeMeasurement(methodName: String, algorithm: String) {
        val ms = this.getMethodStats(methodName, algorithm)

        try {
            val itStart = ms.iterationsStart[ms.itNumber]
            ms.itDurations += Duration.of(System.currentTimeMillis() - itStart, ChronoUnit.MILLIS)
        }
        catch (e: ArrayIndexOutOfBoundsException) {
            log.debug("Statistics: an $e occurred while measuring iteration #${ms.itNumber} time," +
                    " in $methodName using $algorithm algorithm. Duration.ZERO recorded")
            ms.itDurations += Duration.ZERO
        }
        ms.itNumber++
        return
    }

    /**
     * Measuring coverage dynamically  **/
    // FIXME: 17.05.2021


    /**
     * Measuring elapsed time + iterations count  **/

    fun measureOverallTime(methodName: String, algorithm: String) {
        this.getMethodStats(methodName, algorithm).startTime = System.currentTimeMillis()
    }

    fun stopTimeMeasurement(methodName: String, algorithm: String) {
        val ms = this.getMethodStats(methodName, algorithm)
        ms.elapsedTime = Duration.of(System.currentTimeMillis() - ms.startTime, ChronoUnit.MILLIS)
    }


    /**
     * Setting total coverage + total branch coverage  **/

    fun setTotalCoverageValues(methodName: String, algorithm: String, total: Double, branch: Double) {
        val ms = this.getMethodStats(methodName, algorithm)
        ms.totalCoverage = total
        ms.totalBranchCoverage = branch
    }


    /**
     * Measuring average project coverage  **/
    fun countAvgCoverage() {
        var coverage = 0.0
        var branchCoverage = 0.0
        methodHolder.forEach { coverage += it.totalCoverage
            branchCoverage += it.totalBranchCoverage }

        avgCoverage = coverage / methodHolder.size
        avgBranchCoverage = branchCoverage / methodHolder.size
    }

    /**
     * Measuring branch selection time  **/

    fun stopBranchSelectionMeasurement(methodName: String, algorithm: String) {
        val ms = this.getMethodStats(methodName, algorithm)

        try {
            val itStart = ms.iterationsStart[ms.itNumber]
            ms.branchSelectionDuration[ms.itNumber] = Duration.of(
                System.currentTimeMillis() - itStart, ChronoUnit.MILLIS)
        }
        catch (e: ArrayIndexOutOfBoundsException) {
            log.debug("Statistics: an $e occurred while measuring iteration #${ms.itNumber} time," +
                    " in $methodName using $algorithm algorithm. Duration.ZERO recorded")
            ms.branchSelectionDuration[ms.itNumber] = Duration.ZERO
        }
        return
    }

    /**
     * Measuring total number of solver requests  **/

    fun incrementSolverRequests(methodName: String, algorithm: String) {
        this.getMethodStats(methodName, algorithm).solverCalls++
    }


    companion object {
        private var instance: Statistics? = null
        operator fun invoke() = synchronized(this) {
            if(instance == null)
                instance = Statistics()
            instance
        }

        val methodHolder = mutableSetOf<MethodStats>()
        var avgCoverage = 0.0
        var avgBranchCoverage = 0.0

    }

}

data class MethodStats(val algorithm: String,
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
    var totalCoverage = 0.0
    var totalBranchCoverage = 0.0

    var branchSelectionDuration = mutableListOf<Duration>()

    var solverCalls = 0

    fun isEmpty() = startTime <= 0.toLong()
    fun isNotEmpty() = !this.isEmpty()

    override fun hashCode() = super.hashCode() + algorithm.hashCode() + methodName.hashCode() + startTime.hashCode()

    override fun toString(): String {
        return super.toString()
    }
    override fun equals(other: Any?) =
        if(other is MethodStats)
            this.algorithm == other.algorithm && this.methodName == other.methodName &&
                    this.itNumber == other.itNumber && this.itDurations == other.itDurations &&
                    this.startTime == other.startTime && this.elapsedTime == other.elapsedTime &&
                    this.totalCoverage == other.totalCoverage && this.totalBranchCoverage == other.totalBranchCoverage &&
                    this. branchSelectionDuration == other.branchSelectionDuration && this.solverCalls == other.solverCalls
        else false


}