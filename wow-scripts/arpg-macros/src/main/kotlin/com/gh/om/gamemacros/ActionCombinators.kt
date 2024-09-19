package com.gh.om.gamemacros

import java.time.Duration
import java.time.Instant
import java.util.concurrent.atomic.AtomicReference

// XXX These must be thread safe
object ActionCombinators {
    fun unconditionallySkipIfTooFrequent(
        frequency: Duration,
        action: () -> Unit,
    ): () -> Unit {
        var lastTimeFired: Instant? = null

        return {
            val ltf = lastTimeFired
            val now = Instant.now()
            if (ltf == null || now.isAfter(ltf.plus(frequency))) {
                action()
                lastTimeFired = now
            }
            // Otherwise skip
        }
    }

    fun roundRobin(actions: List<() -> Unit>): () -> Unit {
        require(actions.isNotEmpty())

        var nextIx = 0
        return {
            val action = actions[nextIx]
            nextIx = (nextIx + 1) % actions.size
            action()
        }
    }

    class SkipIfTooFrequent(
        private val frequency: Duration,
        private val conditionalAction: () -> Boolean,
        private val getNow: () -> Instant = Instant::now,
    ) : () -> Boolean {
        private val lastTimeFiredRef = AtomicReference(UNINITIALIZED)

        val lastTimeFired: Instant?
            get() {
                val ltf = lastTimeFiredRef.get()
                if (ltf === BEING_FIRED || ltf === UNINITIALIZED) {
                    return null
                }
                return ltf
            }

        /**
         * @return True if the action is triggered.
         */
        override fun invoke(): Boolean {
            val now = getNow()
            val ltf = lastTimeFiredRef.getAndSet(BEING_FIRED)
            if (ltf === BEING_FIRED) {
                // Is being fired by someone else: Already too frequent.
                return false
            }
            if (ltf === UNINITIALIZED || now.isAfter(ltf.plus(frequency))) {
                val fired = conditionalAction()
                if (fired) {
                    lastTimeFiredRef.set(now)
                    return true
                }
            }
            // "Unlock" the ref
            lastTimeFiredRef.set(ltf)
            return false
        }

        companion object {
            private val BEING_FIRED = Instant.now()
            private val UNINITIALIZED = Instant.now()
        }
    }
}
