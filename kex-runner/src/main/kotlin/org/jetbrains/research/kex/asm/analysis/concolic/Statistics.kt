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

    /*1. Measuring one iteration time + iterations number*/

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


    /*2. Measuring coverage dynamically*/




    /*3. Measuring elapsed time + iterations count*/

    fun measureOverallTime(methodName: String, algorithm: String) {
        this.getMethodStats(methodName, algorithm).startTime = System.currentTimeMillis()
    }

    fun stopTimeMeasurement(methodName: String, algorithm: String) {
        val ms = this.getMethodStats(methodName, algorithm)
        ms.elapsedTime = Duration.of(System.currentTimeMillis() - ms.startTime, ChronoUnit.MILLIS)
    }


    /*4. Setting total coverage + total branch coverage*/

    fun setTotalCoverageValues(methodName: String, algorithm: String, total: Double, branch: Double) {
        val ms = this.getMethodStats(methodName, algorithm)
        ms.totalCoverage = total
        ms.totalBranchCoverage = branch
    }


    /*5. Average project coverage*/
    fun countAvgCoverage() {
        var coverage = 0.0
        var branchCoverage = 0.0
        methodHolder.forEach { coverage += it.totalCoverage
            branchCoverage += it.totalBranchCoverage }

        avgCoverage = coverage / methodHolder.size
        avgBranchCoverage = branchCoverage / methodHolder.size
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
    var itNumber = 1

    val iterationsStart = mutableListOf<Long>()
    val itDurations = mutableListOf<Duration>()



    var startTime = 0.toLong()
    var elapsedTime = Duration.ZERO!!

    var totalCoverage = 0.0
    var totalBranchCoverage = 0.0


    fun isEmpty() = true
    fun isNotEmpty() = !this.isEmpty()

    override fun hashCode(): Int {
        return super.hashCode()
    }
    override fun toString(): String {
        return super.toString()
    }
    override fun equals(other: Any?): Boolean {
        return super.equals(other)
    }
}
