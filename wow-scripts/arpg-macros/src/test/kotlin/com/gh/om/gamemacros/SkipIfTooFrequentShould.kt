package com.gh.om.gamemacros

import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.async
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.runBlocking
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test
import java.time.Duration
import java.time.Instant
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicReference

data class Buff(
    val version: Int,
    val startTime: Instant,
) {
    fun repr(
        from: Instant,
    ): String {
        val elapsed = Duration.between(from, startTime)
        return "Buff(v$version, elapsed = $elapsed)"
    }
}

class ClockMocks {
    val testStart = Instant.now()
    val nowRef = AtomicReference(testStart)

    fun getNow() = nowRef.get()
}

class BuffMocks(
    val clock: ClockMocks = ClockMocks(),
    val effectCheckIsWorking: Boolean = true,
    val buffDuration: Duration = Duration.ofSeconds(5),
) {
    val buffRef = AtomicReference<Buff>()
    val buffHistory = mutableListOf<Buff>()

    val testStart
        get() = clock.testStart

    val isConditionalActionEntered = AtomicBoolean()

    fun reportBuffHistory(): String {
        return buffHistory.joinToString { it.repr(testStart) }
    }

    fun getNow() = clock.getNow()

    fun isInEffect(): Boolean {
        if (!effectCheckIsWorking) {
            // Useful for testing throttle when the actual buff check fails.
            return false
        }
        val buff = buffRef.get() ?: return false
        return Duration.between(buff.startTime, getNow()) < buffDuration
    }

    fun updateBuff(oldBuff: Buff?): Buff {
        val newVersion = if (oldBuff == null) {
            0
        } else {
            oldBuff.version + 1
        }
        return Buff(newVersion, getNow())
    }

    suspend fun conditionalAction(): Boolean {
        require(!isConditionalActionEntered.getAndSet(true))
        try {
            if (isInEffect()) {
                return false
            }
            val newBuff = buffRef.updateAndGet(::updateBuff)
            synchronized(buffHistory) {
                buffHistory += newBuff
            }
            return true
        } finally {
            require(isConditionalActionEntered.getAndSet(false))
        }
    }
}

class SkipIfTooFrequentShould {
    @Test
    fun `throttle thread safely`() {
        val mocks = BuffMocks(effectCheckIsWorking = false)

        val target = ActionCombinators.SkipIfTooFrequent(
            frequency = Duration.ofSeconds(1),
            conditionalAction = mocks::conditionalAction,
            getNow = mocks::getNow,
        )

        runBlocking(Dispatchers.IO) {
            val nTasks = 100
            val nRep = 500
            val completionCount = AtomicInteger()
            val tasks = List(nTasks) {
                async {
                    repeat(nRep) {
                        target()
                        if (completionCount.incrementAndGet() == (nTasks * nRep / 2)) {
                            // Half way: advance clock
                            mocks.clock.nowRef.updateAndGet {
                                it.plusSeconds(10)
                            }
                        }
                    }
                }
            }
            tasks.joinAll()
        }
        println("Buff history: ${mocks.reportBuffHistory()}")
        assertThat(mocks.buffRef.get().version).isEqualTo(1)
    }

    @Test
    fun `throttle thread safely 2`() {
        val mocks = BuffMocks()

        val target = ActionCombinators.SkipIfTooFrequent(
            frequency = Duration.ofSeconds(1),
            conditionalAction = mocks::conditionalAction,
            getNow = mocks::getNow,
        )

        runBlocking(Dispatchers.IO) {
            val nTasks = 100
            val nRep = 500
            val completionCount = AtomicInteger()
            val tasks = List(nTasks) {
                async {
                    repeat(nRep) {
                        target()
                        // mocks.clock.nowRef.updateAndGet { it.plusMillis(1) }
                    }
                }
            }
            tasks.joinAll()
        }
        println("Buff history: ${mocks.reportBuffHistory()}")
        assertThat(mocks.buffRef.get().version).isEqualTo(1)
    }
}
