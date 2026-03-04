package com.gh.om.ks.arpgmacro.core.buff

import com.gh.om.ks.arpgmacro.core.Clock
import kotlinx.coroutines.async
import kotlinx.coroutines.coroutineScope
import java.time.Duration
import java.time.Instant
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicReference
import kotlin.time.Duration.Companion.milliseconds

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

class BuffManager(private val clock: Clock, private val keeper: BuffKeeper) {
    suspend fun useAll() {
        keeper.triggerUndetectably(clock)
    }

    /**
     * @param getTimestampForActivePlaying The last timestamp when a key that triggers
     * the buff was pressed
     * @param isGameActive True if the gap fixer should also be running
     * @param buffLingering The maximum flask downtime to "resurrect" it
     * @param inputLingering The maximum input downtime to "resurrect" flasks
     */
    suspend fun runGapFixer(
        getTimestampForActivePlaying: () -> Instant,
        isGameActive: () -> Boolean,
        buffLingering: Duration = Duration.ofSeconds(2),
        inputLingering: Duration = Duration.ofSeconds(5),
    ) {
        suspend fun once() {
            if (!isGameActive()) return

            keeper.isBuffInEffect()

            val now = Instant.ofEpochMilli(clock.currentTimeMillis())
            val lastTimeActivelyPlaying = getTimestampForActivePlaying()
            val lastTimeBuffHadEffect = keeper.lastTimeBuffHadEffect ?: return
            val playingElapsed = Duration.between(lastTimeActivelyPlaying, now)
            val buffElapsed = Duration.between(lastTimeBuffHadEffect, now)
            if (playingElapsed > inputLingering || buffElapsed > buffLingering) {
                return
            } else {
                useAll()
            }
        }

        while (true) {
            once()
            clock.delay(100.milliseconds)
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

    // Deliberately avoiding short-circuiting, since isBuffInEffect has side effects
    override fun isBuffInEffect() = keepers.map { it.isBuffInEffect() }.all { it }

    override fun trigger(): Boolean = keepers.map { it.trigger() }.any { it }
}

suspend fun BuffKeeper.triggerUndetectably(clock: Clock) {
    if (this is ParallelBuffKeeper) {
        // Avoid using all at the same time
        coroutineScope {
            keepers.map {
                async {
                    clock.delay(0.milliseconds, extraVarianceMs = randomDelayMs)
                    it.trigger()
                }
            }.map { it.await() }.any { it }
        }
    } else {
        trigger()
    }
}

class AlternatingBuffKeeper(
    private val keepers: List<BuffKeeper>,
    clock: Clock,
    // Around a couple of frames to leave time for flask buff to show
    throttle: Duration = Duration.ofMillis(500),
) : BuffKeeper {
    private val nextIxRef = AtomicInteger()
    private val getNow: () -> Instant = { Instant.ofEpochMilli(clock.currentTimeMillis()) }

    // Need one more layer of throttle here, since each keeper's internal
    // throttle state is independent, and won't prevent other keepers from overfiring.
    private val throttledUse = SkipIfTooFrequent(
        getNow = getNow,
        frequency = throttle,
        conditionalAction = ::triggerInternal,
    )

    override val lastTimeBuffWasApplied: Instant?
        get() = keepers.mapNotNull { it.lastTimeBuffWasApplied }.maxOrNull()

    override val lastTimeBuffHadEffect: Instant?
        get() = keepers.mapNotNull { it.lastTimeBuffHadEffect }.maxOrNull()

    override fun isBuffInEffect(): Boolean = keepers.map { it.isBuffInEffect() }.any { it }

    override fun trigger() = throttledUse()

    private fun triggerInternal(): Boolean {
        // Shouldn't trigger if any is in effect
        if (isBuffInEffect()) {
            // Still return true to throttle
            return true
        }
        val nextIx = nextIxRef.getAndUpdate { (it + 1) % keepers.size }
        keepers[nextIx].trigger()
        return true
    }
}

class SingleBuffKeeper(
    clock: Clock,
    throttle: Duration = Duration.ofSeconds(1),
    private val applyBuff: () -> Unit,
    private val isBuffInEffect: () -> Boolean,
) : BuffKeeper {
    private val getNow: () -> Instant = { Instant.ofEpochMilli(clock.currentTimeMillis()) }

    override fun isBuffInEffect(): Boolean {
        val inEffect = this.isBuffInEffect.invoke()
        if (inEffect) {
            lastTimeBuffHadEffect = getNow()
        }
        return inEffect
    }

    override fun trigger() = throttledUse()

    override val lastTimeBuffWasApplied: Instant?
        get() = throttledUse.lastTimeFired

    override var lastTimeBuffHadEffect: Instant? = null
        private set

    private val throttledUse = SkipIfTooFrequent(
        getNow = getNow,
        frequency = throttle,
        conditionalAction = ::conditionalAction,
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

/**
 * Skips the action if it was triggered too recently.
 * Thread-safe via AtomicReference sentinel pattern.
 */
private class SkipIfTooFrequent(
    private val frequency: Duration,
    private val conditionalAction: () -> Boolean,
    private val getNow: () -> Instant,
) : () -> Boolean {
    private val lastTimeFiredRef = AtomicReference(UNINITIALIZED)

    val lastTimeFired: Instant?
        get() {
            val ltf = lastTimeFiredRef.get()
            return if (ltf === BEING_FIRED || ltf === UNINITIALIZED) null else ltf
        }

    override fun invoke(): Boolean {
        val now = getNow()
        val ltf = lastTimeFiredRef.getAndSet(BEING_FIRED)
        if (ltf === BEING_FIRED) {
            return false
        }
        if (ltf === UNINITIALIZED || now.isAfter(ltf.plus(frequency))) {
            val fired = conditionalAction()
            if (fired) {
                lastTimeFiredRef.set(now)
                return true
            }
        }
        lastTimeFiredRef.set(ltf)
        return false
    }

    companion object {
        private val BEING_FIRED = Instant.now()
        private val UNINITIALIZED = Instant.now()
    }
}
