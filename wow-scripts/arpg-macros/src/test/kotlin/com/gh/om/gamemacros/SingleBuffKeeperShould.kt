package com.gh.om.gamemacros

import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.async
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.runBlocking
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test
import java.time.Duration
import java.time.Instant
import java.util.concurrent.atomic.AtomicInteger
import kotlin.test.Ignore

private class TestSingleBuffKeeper(private val mocks: BuffMocks) : BuffKeeper {
    override fun isBuffInEffect(): Boolean {
        return mocks.isInEffect()
    }

    override fun trigger() = mocks.conditionalAction()

    override val lastTimeBuffWasApplied: Instant? = null
    override val lastTimeBuffHadEffect: Instant? = null

}

class AlternatingBuffKeeperShould {
    @Ignore
    @Test
    fun `be thread safe`() {
        val clock = ClockMocks()
        val keeperCount = 3
        val mocks =
            List(keeperCount) {
                BuffMocks(
                    clock,
                    buffDuration = Duration.ofSeconds(2)
                )
            }
        val singleKeepers = mocks.map(::TestSingleBuffKeeper)
        val target = AlternatingBuffKeeper(singleKeepers, clock::getNow)

        runBlocking(Dispatchers.IO) {
            val nTasks = 100
            val nRep = 500

            val clockAdvanceCount = keeperCount * 2 - 1
            val whenToAdvanceClock = List(clockAdvanceCount) {
                10 + (nTasks * nRep) / (clockAdvanceCount * 2) * it
            }

            val completionCount = AtomicInteger()
            val tasks = List(nTasks) {
                async {
                    repeat(nRep) {
                        target.trigger()
                        if (completionCount.incrementAndGet() in whenToAdvanceClock) {
                            clock.nowRef.updateAndGet {
                                it.plusSeconds(2)
                            }
                        }
                    }
                }
            }
            tasks.joinAll()
        }

        for ((i, mock) in mocks.withIndex()) {
            println("Keeper($i): ${mock.reportBuffHistory()}")
        }

        for (mock in mocks) {
            assertThat(mock.buffHistory).hasSize(2)
        }
    }

    @Ignore
    @Test
    fun `work when buff check is bad`() {
        val clock = ClockMocks()
        val keeperCount = 3
        val mocks =
            List(keeperCount) {
                BuffMocks(
                    clock,
                    buffDuration = Duration.ofSeconds(2),
                    effectCheckIsWorking = false
                )
            }
        val singleKeepers = mocks.map(::TestSingleBuffKeeper)
        val target = AlternatingBuffKeeper(singleKeepers, clock::getNow)

        runBlocking {
            val nTasks = 10
            val nRep = 50

            val clockAdvanceCount = keeperCount * 2 - 1
            val whenToAdvanceClock = List(clockAdvanceCount) {
                10 + (nTasks * nRep) / (clockAdvanceCount * 2) * it
            }

            val tasks = List(nTasks) {
                async {
                    repeat(nRep) {
                        target.trigger()
                        clock.nowRef.updateAndGet {
                            it.plusMillis(500)
                        }
                    }
                }
            }
            tasks.joinAll()
        }

        for ((i, mock) in mocks.withIndex()) {
            println("Keeper($i): ${mock.reportBuffHistory()}")
        }

        for (mock in mocks) {
            assertThat(mock.buffHistory).hasSize(2)
        }
    }
}
