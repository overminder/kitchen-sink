package com.gh.om.ks.arpgmacro.core.overlay

import com.gh.om.ks.arpgmacro.core.KeyboardInput
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.flow

/**
 * Simplified leader key listener for v3. Just detects the Alt+X chord
 * and emits a signal — no command parsing, no state machine, no timer management.
 *
 * The coordinator handles all state after the leader key fires.
 */
class LeaderKeyListener(
    private val leaderChord: Set<String>,
    private val keyboardInput: KeyboardInput,
) {
    init {
        require(leaderChord.isNotEmpty())
    }

    /**
     * Emits Unit each time the leader chord is detected (key releases matching the chord).
     * Collect this flow and call coordinator.onLeaderKey() for each emission.
     */
    fun leaderKeyEvents(): Flow<Unit> = flow {
        val buffer = mutableListOf<String>()
        keyboardInput.keyReleases().collect { key ->
            buffer += key
            if (buffer.size > leaderChord.size) {
                buffer.removeAt(0)
            }
            if (buffer.size == leaderChord.size && buffer.toSet() == leaderChord) {
                buffer.clear()
                emit(Unit)
            }
        }
    }
}
