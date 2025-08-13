@file:OptIn(ExperimentalCoroutinesApi::class)

package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.KeyHooks
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.mapLatest
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

class LeaderKeyDetector(
    private val leaderKey: Set<String>,
    private val gracePeriod: Duration = 1.seconds,
) {
    init {
        require(leaderKey.isNotEmpty())
    }

    fun isEnabled(command: String): Flow<Boolean> {
        require(command.isNotEmpty())

        val commandList = command.toList().map { it.toString() }
        // The idea is that a flow that keeps track of the currently pressed
        // sequence since leader key, plus a grace period at the end.
        var keySequence = mutableListOf<String>()

        val totalLength = leaderKey.size + commandList.size

        fun handleRelease(key: String): Boolean {
            keySequence += key
            if (keySequence.size >= leaderKey.size) {
                // Check if leader key is fully typed
                if (keySequence.take(leaderKey.size).toSet() == leaderKey) {
                    // Yes. Fall through.
                } else {
                    // throw first char away.
                    keySequence.removeAt(0)
                    return false
                }
            }
            // Check if rest of keys match.
            val receivedEnough = keySequence.size >= totalLength
            if (!receivedEnough) {
                return false
            }
            val found = keySequence
                .drop(leaderKey.size)
                .take(commandList.size) == commandList
            // Regardless of whether a match is found, clear the history.
            keySequence = keySequence.drop(totalLength).toMutableList()
            return found
        }
        return KeyHooks.keyReleases().mapLatest {
            val result = handleRelease(it)
            delay(gracePeriod)
            result
        }
    }
}

val LEADER_KEY = LeaderKeyDetector(setOf("Alt", "X"))
