package com.gh.om.gamemacros

import java.time.Duration
import java.time.Instant

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

    class SkipIfTooFrequent<A>(
        private val frequency: Duration,
        private val conditionalAction: (A) -> Boolean,
    ) : (A) -> Boolean {
        var lastTimeFired: Instant? = null
            private set

        /**
         * @return True if the action is triggered.
         */
        override fun invoke(input: A): Boolean {
            val ltf = lastTimeFired
            val now = Instant.now()
            if (ltf == null || now.isAfter(ltf.plus(frequency))) {
                val fired = conditionalAction(input)
                if (fired) {
                    lastTimeFired = now
                    return true
                }
            }
            return false
        }
    }
}
