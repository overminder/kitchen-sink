package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.postPressRelease
import com.gh.om.ks.arpgmacro.di.GameType
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.collectLatest
import kotlinx.coroutines.flow.distinctUntilChanged
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.onStart
import kotlinx.coroutines.flow.stateIn
import kotlinx.coroutines.launch
import javax.inject.Inject
import kotlin.time.Duration.Companion.milliseconds

/**
 * Background macro for Diablo IV: while W is held, triggers skills 2/3 on round-robin at 50ms;
 * while R is held, triggers skill 4 at 50ms.
 *
 * Ports [GameSpecific.triggerSkillsInD4].
 */
class TriggerSkillsD4Macro @Inject constructor(
    private val activeWindowChecker: ActiveWindowChecker,
    private val keyboardInput: KeyboardInput,
    private val keyboardOutput: KeyboardOutput,
    private val clock: Clock,
) {
    suspend fun run(isEnabled: StateFlow<Boolean>, keyboardOutput: KeyboardOutput = this.keyboardOutput) {
        coroutineScope {
            val isD4 = activeWindowChecker.activeWindowFlow(setOf(GameTitles.from(GameType.Diablo4)))
                .stateIn(this)

            fun active() = isEnabled.value && isD4.value

            // W held: round-robin 2 and 3
            launch {
                var nextKey = 0
                val keys = listOf("2", "3")
                keyboardInput.keyStates()
                    .map { "W" in it }
                    .distinctUntilChanged()
                    .onStart { emit(false) }
                    .collectLatest { held ->
                        while (active() && held) {
                            keyboardOutput.postPressRelease(keys[nextKey])
                            nextKey = (nextKey + 1) % keys.size
                            clock.delay(50.milliseconds)
                        }
                    }
            }

            // R held: trigger 4
            keyboardInput.keyStates()
                .map { "R" in it }
                .distinctUntilChanged()
                .onStart { emit(false) }
                .collectLatest { held ->
                    while (active() && held) {
                        keyboardOutput.postPressRelease("4")
                        clock.delay(50.milliseconds)
                    }
                }
        }
    }
}
