package com.gh.om.gamemacros

import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlinx.coroutines.time.delay
import java.time.Duration
import java.time.Instant
import java.util.concurrent.atomic.AtomicInteger

interface BuffKeeper {
    fun isBuffInEffect(): Boolean

    /**
     * @return True if any of the buff was indeed triggered
     */
    fun trigger(): Boolean

    /**
     * The start time of the latest buff
     */
    val lastTimeBuffWasApplied: Instant?

    /**
     * Just before the end time of the latest buff
     */
    val lastTimeBuffHadEffect: Instant?
}

class BuffManager(private val keeper: BuffKeeper) {
    suspend fun useAll() {
        keeper.triggerUndetectably()
    }

    /**
     * @param getTimestampForActivePlaying The last timestamp when a key that triggers
     * the buff was pressed
     * @param isGameActive True if the gap fixer should also be running
     * @param buffLingering The maximum flask downtime to "resurrect" it
     * @param inputLingering The maximum input downtime to "resurrect"
     * flasks
     */
    suspend fun runGapFixer(
        getTimestampForActivePlaying: () -> Instant,
        isGameActive: () -> Boolean,
        buffLingering: Duration = Duration.ofSeconds(2),
        inputLingering: Duration = Duration.ofSeconds(5),
    ) {
        suspend fun once() {
            if (!isGameActive()) {
                return
            }

            // Check buffs again
            keeper.isBuffInEffect()

            val now = Instant.now()
            val lastTimeActivelyPlaying = getTimestampForActivePlaying()
            val lastTimeBuffHadEffect =
                keeper.lastTimeBuffHadEffect ?: return
            val playingElapsed =
                Duration.between(lastTimeActivelyPlaying, now)
            val buffElapsed =
                Duration.between(lastTimeBuffHadEffect, now)
            if (playingElapsed > inputLingering
                || buffElapsed > buffLingering
            ) {
                return
            } else {
                useAll()
            }
        }

        while (true) {
            once()
            safeDelay(Duration.ofMillis(100))
        }
    }
}

class ParallelBuffKeeper(
    val keepers: List<BuffKeeper>,
    val randomDelayMs: Long = 20,
) : BuffKeeper {

    override val lastTimeBuffWasApplied: Instant?
        get() = keepers.mapNotNull { it.lastTimeBuffWasApplied }.maxOrNull()

    override val lastTimeBuffHadEffect: Instant?
        get() = keepers.mapNotNull { it.lastTimeBuffHadEffect }.maxOrNull()

    // Deliberately avoiding short-circuiting, since isBuffInEffect has
    // side effects lol
    override fun isBuffInEffect() = keepers
        .map { it.isBuffInEffect() }
        .all { it }

    override fun trigger(): Boolean {
        return keepers.map { it.trigger() }.any { it }
    }
}

suspend fun BuffKeeper.triggerUndetectably() {
    if (this is ParallelBuffKeeper) {
        // Avoid using all at the same time
        keepers.map {
            currentCoroutineScope().async {
                safeDelay(Duration.ZERO, randomDelayMs)
                it.trigger()
            }
        }.awaitAll().any { it }
    } else {
        trigger()
    }
}

class AlternatingBuffKeeper(
    private val keepers: List<BuffKeeper>,
    getNow: () -> Instant = Instant::now,
    // Around a couple of frames to leave time for flask buff to show
    // XXX This is much more than a couple of frames!
    throttle: Duration = Duration.ofMillis(500),
) : BuffKeeper {
    private val nextIxRef = AtomicInteger()

    // Need one more layer of throttle here, since each keeper's internal
    // throttle state is independent, and won't prevent other keepers
    // from overfiring.
    private val throttledUse = ActionCombinators.SkipIfTooFrequent(
        getNow = getNow,
        frequency = throttle,
        conditionalAction = ::triggerInternal,
    )

    override val lastTimeBuffWasApplied: Instant?
        get() = keepers.mapNotNull { it.lastTimeBuffWasApplied }.maxOrNull()

    override val lastTimeBuffHadEffect: Instant?
        get() = keepers.mapNotNull { it.lastTimeBuffHadEffect }.maxOrNull()

    override fun isBuffInEffect(): Boolean {
        return keepers.map { it.isBuffInEffect() }.any { it }
    }

    override fun trigger() = throttledUse()

    private fun triggerInternal(): Boolean {
        // Shouldn't trigger if any is in effect
        if (isBuffInEffect()) {
            // Still return true to throttle
            return true
        }

        val nextIx = nextIxRef.getAndUpdate {
            (it + 1) % keepers.size
        }
        val keeper = keepers[nextIx]
        keeper.trigger()
        return true
    }
}

class SingleBuffKeeper(
    throttle: Duration = Duration.ofSeconds(1),
    private val getNow: () -> Instant = Instant::now,
    private val applyBuff: () -> Unit,
    private val isBuffInEffect: () -> Boolean,
) : BuffKeeper {
    override fun isBuffInEffect(): Boolean {
        val inEffect = this.isBuffInEffect.invoke()
        if (inEffect) {
            lastTimeBuffHadEffect = getNow()
        }
        return inEffect
    }

    override fun trigger() = throttledUse()

    override val lastTimeBuffWasApplied
        get() = throttledUse.lastTimeFired

    override var lastTimeBuffHadEffect: Instant? = null
        private set

    private val throttledUse = ActionCombinators.SkipIfTooFrequent(
        getNow = getNow,
        frequency = throttle,
        conditionalAction = ::conditionalAction
    )

    private fun conditionalAction(): Boolean {
        return if (isBuffInEffect()) {
            false
        } else {
            applyBuff()
            true
        }
    }
}

class KeySequencer(
    private val runKeys: List<suspend () -> Unit>,
) : suspend () -> Unit {
    override suspend fun invoke() {
        for (k in runKeys) {
            k()
        }
    }

    companion object {
        fun from(
            keyAndCastRates: List<Pair<String, Double>>,
        ): KeySequencer {
            val runKeys = keyAndCastRates.map { (key, castRate) ->
                val backswingTime = (1000 / castRate).toLong()
                suspend {
                    KeyHooks.postAsciiString(key)
                    safeDelay(Duration.ofMillis(backswingTime))
                }
            }
            return KeySequencer(runKeys)
        }

        /**
         * Alternates between the keys and press times.
         * A string can contain more than one chars, which will be pressed
         * together and released together.
         *
         * The press time is in milliseconds.
         */
        fun fromLongPress(
            keyAndPressTimes: List<Pair<String, Long>>,
            gap: Duration = Duration.ofMillis(25),
        ): KeySequencer {
            val runKeys = keyAndPressTimes.map { (keys, pressTime) ->
                suspend {
                    KeyHooks.postPressWaitRelease(
                        keys.map(::getKeyCodeFromAsciiChar),
                        Duration.ofMillis(pressTime)
                    )
                    delay(gap)
                }
            }
            return KeySequencer(runKeys)
        }

        fun shortPressWithInterval(
            keys: String,
            gapBefore: Duration = Duration.ofMillis(200),
            gapAfter: Duration = Duration.ofMillis(200),
            duration: Duration = Duration.ofMillis(200),
        ): KeySequencer {
            val runKeys = listOf(
                suspend {
                    delay(gapBefore)
                    KeyHooks.postPressWaitRelease(
                        keys.map(::getKeyCodeFromAsciiChar),
                        duration
                    )
                    delay(gapAfter)
                }
            )
            return KeySequencer(runKeys)
        }
    }
}
