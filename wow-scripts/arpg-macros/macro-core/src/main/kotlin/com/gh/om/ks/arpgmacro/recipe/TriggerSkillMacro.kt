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
import javax.inject.Inject
import kotlin.time.Duration.Companion.milliseconds

/**
 * Background macro for POE1: presses the focus key (R) while an attack or unearth key (W/S)
 * is held. Disabled for 3s after any travel key (F4-F7) is pressed.
 *
 * Ports [GameSpecific.triggerSkillInPoe].
 */
class TriggerSkillMacro @Inject constructor(
    private val activeWindowChecker: ActiveWindowChecker,
    private val keyboardInput: KeyboardInput,
    private val keyboardOutput: KeyboardOutput,
    private val clock: Clock,
) {
    suspend fun run(isEnabled: StateFlow<Boolean>) {
        coroutineScope {
            val isPoe = activeWindowChecker.activeWindowFlow(setOf(GameTitles.from(GameType.POE1)))
                .stateIn(this)
            val triggerEnabled = keyboardInput.triggerKeyEnabledFlow(setOf("F4", "F5", "F6", "F7"))
                .stateIn(this)

            fun active() = isEnabled.value && isPoe.value && triggerEnabled.value

            keyboardInput.keyStates()
                .map { pressed -> "W" in pressed || "S" in pressed }
                .distinctUntilChanged()
                .onStart { emit(false) }
                .collectLatest { inputHeld ->
                    while (active() && inputHeld) {
                        keyboardOutput.postPressRelease("R")
                        clock.delay(2.milliseconds, extraVarianceMs = 0)
                    }
                }
        }
    }
}
