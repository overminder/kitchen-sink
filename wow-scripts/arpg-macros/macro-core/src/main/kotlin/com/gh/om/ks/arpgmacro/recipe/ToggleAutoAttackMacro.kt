package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.di.GameType
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.collectLatest
import kotlinx.coroutines.flow.distinctUntilChanged
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.stateIn
import kotlinx.coroutines.flow.update
import kotlinx.coroutines.launch
import javax.inject.Inject
import kotlin.time.Duration.Companion.milliseconds

/**
 * Background macro for POE1 simulacrum: toggles continuous hold-attack (W) on D press,
 * resets the toggle on E (move) press. While toggled, holds W for 500ms intervals.
 *
 * Ports [GameSpecific.toggleAutoAttackInPoe].
 */
class ToggleAutoAttackMacro @Inject constructor(
    private val activeWindowChecker: ActiveWindowChecker,
    private val keyboardInput: KeyboardInput,
    private val keyboardOutput: KeyboardOutput,
    private val clock: Clock,
) {
    suspend fun run(isEnabled: StateFlow<Boolean>, keyboardOutput: KeyboardOutput = this.keyboardOutput) {
        coroutineScope {
            val isPoe = activeWindowChecker.activeWindowFlow(setOf(GameTitles.from(GameType.POE1)))
                .stateIn(this)
            val triggerEnabled = keyboardInput.triggerKeyEnabledFlow(setOf("F4", "F5", "F6", "F7"))
                .stateIn(this)

            fun canRun() = isEnabled.value && isPoe.value && triggerEnabled.value

            val toggled = MutableStateFlow(false)

            // Toggle on D rising edge
            launch {
                var wasPressed = false
                keyboardInput.keyStates()
                    .map { "D" in it }
                    .distinctUntilChanged()
                    .collect { pressed ->
                        if (!wasPressed && pressed) toggled.update { !it && canRun() }
                        wasPressed = pressed
                    }
            }

            // Reset on E (move) press
            launch {
                keyboardInput.keyPresses().collect { key ->
                    if (key == "E") toggled.value = false
                }
            }

            // Hold-attack loop
            toggled.collectLatest { shouldAttack ->
                if (shouldAttack) {
                    while (canRun()) {
                        try {
                            keyboardOutput.postPress("W")
                            clock.delay(500.milliseconds)
                        } finally {
                            // Always release W — if collectLatest cancels this coroutine
                            // mid-hold (e.g. E press), the synthetic W keydown would
                            // otherwise stay stuck in the system.
                            keyboardOutput.postRelease("W")
                        }
                        clock.delay(25.milliseconds)
                    }
                    toggled.value = false
                }
            }
        }
    }
}
