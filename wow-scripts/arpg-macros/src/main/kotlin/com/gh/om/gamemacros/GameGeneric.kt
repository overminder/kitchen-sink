package com.gh.om.gamemacros

import kotlinx.coroutines.async
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.time.delay
import java.time.Duration
import java.time.Instant
import kotlin.random.Random

interface BuffKeeper {
    fun isBuffInEffect(): Boolean
    suspend fun trigger()

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
        // Avoid using all at the same time
        keeper.trigger()
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
            delay(Duration.ofMillis(100))
        }
    }
}

class ParallelBuffKeeper(
    private val keepers: List<BuffKeeper>,
    private val randomDelayMs: Long = 20,
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

    override suspend fun trigger() {
        keepers.map {
            currentCoroutineScope().async {
                delay(Duration.ofMillis(Random.nextLong(randomDelayMs)))
                it.trigger()
            }
        }.joinAll()
    }
}

class AlternatingBuffKeeper(
    val keepers: List<BuffKeeper>,
) : BuffKeeper {
    private var nextIx = 0

    override val lastTimeBuffWasApplied: Instant?
        get() = keepers.mapNotNull { it.lastTimeBuffWasApplied }.maxOrNull()

    override val lastTimeBuffHadEffect: Instant?
        get() = keepers.mapNotNull { it.lastTimeBuffHadEffect }.maxOrNull()

    override fun isBuffInEffect(): Boolean {
        return keepers.map { it.isBuffInEffect() }.any { it }
    }

    override suspend fun trigger() {
        // Shouldn't trigger if any is in effect
        if (isBuffInEffect()) {
            return
        }

        val keeper = keepers[nextIx]
        keeper.trigger()
        nextIx = (nextIx + 1) % keepers.size
    }
}

class SingleBuffKeeper(
    throttle: Duration = Duration.ofSeconds(1),
    private val applyBuff: () -> Unit,
    private val isBuffInEffect: () -> Boolean,
) : BuffKeeper {
    override fun isBuffInEffect(): Boolean {
        val inEffect = this.isBuffInEffect.invoke()
        if (inEffect) {
            lastTimeBuffHadEffect = Instant.now()
        }
        return inEffect
    }

    override suspend fun trigger() {
        throttledUse(Unit)
    }

    override val lastTimeBuffWasApplied
        get() = throttledUse.lastTimeFired

    override var lastTimeBuffHadEffect: Instant? = null
        private set

    private val throttledUse = ActionCombinators.SkipIfTooFrequent(
        throttle,
        ::conditionalAction
    )

    private fun conditionalAction(
        @Suppress("UNUSED_PARAMETER") ignored: Unit
    ): Boolean {
        return if (isBuffInEffect()) {
            false
        } else {
            applyBuff()
            true
        }
    }
}
