package com.gh.om.ks.arpgmacro.core

import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.flow
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

/**
 * Vim-style leader key detector. Listens to key releases and detects
 * leader+command chords.
 *
 * Fixes over the original implementation:
 * 1. Activates immediately on match (no 1-second delay before activation)
 * 2. Stray key releases don't cancel pending activation
 * 3. Partial sequences timeout after grace period
 * 4. State machine has explicit phases (no redundant leader re-validation)
 */
class LeaderKeyDetector(
    private val leaderKey: Set<String>,
    private val keyboardInput: KeyboardInput,
    private val clock: Clock,
    private val timeout: Duration = 2.seconds,
    private val onLeaderActivated: () -> Unit = {},
    private val onLeaderDeactivated: () -> Unit = {},
) {
    private val commands = mutableSetOf<String>()

    // Deduplicate callbacks across parallel isEnabled flows
    private val leaderActive = AtomicBoolean(false)

    init {
        require(leaderKey.isNotEmpty())
    }

    /**
     * Returns a Flow that emits `true` when the leader+command chord is detected,
     * and `false` otherwise. The activation is immediate on match.
     */
    fun isEnabled(command: String): Flow<Boolean> {
        require(command.isNotEmpty())
        require(commands.add(command)) { "Command $command is already registered" }

        val commandKeys = command.toList().map { it.toString() }

        return flow {
            var state: DetectorState = DetectorState.WaitingForLeader
            var keyBuffer = mutableListOf<String>()
            var leaderMatchedAt: Long? = null

            keyboardInput.keyReleases().collect { key ->
                when (val s = state) {
                    is DetectorState.WaitingForLeader -> {
                        keyBuffer += key
                        if (keyBuffer.size > leaderKey.size) {
                            keyBuffer.removeAt(0)
                        }
                        if (keyBuffer.size == leaderKey.size && keyBuffer.toSet() == leaderKey) {
                            state = DetectorState.WaitingForCommand(collected = mutableListOf())
                            leaderMatchedAt = clock.currentTimeMillis()
                            keyBuffer = mutableListOf()
                            if (leaderActive.compareAndSet(false, true)) {
                                onLeaderActivated()
                            }
                        }
                    }

                    is DetectorState.WaitingForCommand -> {
                        // Check timeout
                        val elapsed = clock.currentTimeMillis() - (leaderMatchedAt ?: 0)
                        if (elapsed > timeout.inWholeMilliseconds) {
                            // Timeout: reset
                            state = DetectorState.WaitingForLeader
                            keyBuffer = mutableListOf(key)
                            leaderMatchedAt = null
                            if (leaderActive.compareAndSet(true, false)) {
                                onLeaderDeactivated()
                            }
                            emit(false)
                            return@collect
                        }

                        s.collected += key
                        if (s.collected.size == commandKeys.size) {
                            if (s.collected == commandKeys) {
                                // Match! Emit immediately
                                emit(true)
                            } else {
                                // Mismatch: full reset
                                emit(false)
                            }
                            state = DetectorState.WaitingForLeader
                            keyBuffer = mutableListOf()
                            leaderMatchedAt = null
                            if (leaderActive.compareAndSet(true, false)) {
                                onLeaderDeactivated()
                            }
                        }
                    }
                }
            }
        }
    }

    private sealed class DetectorState {
        data object WaitingForLeader : DetectorState()
        data class WaitingForCommand(val collected: MutableList<String>) : DetectorState()
    }
}
