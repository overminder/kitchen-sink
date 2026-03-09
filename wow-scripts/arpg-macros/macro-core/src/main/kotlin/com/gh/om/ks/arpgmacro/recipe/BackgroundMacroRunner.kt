package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.ReportingKeyboardOutput
import com.gh.om.ks.arpgmacro.core.overlay.BgMacroStatusLine
import com.gh.om.ks.arpgmacro.core.overlay.BgMacroStatusTracker
import com.gh.om.ks.arpgmacro.recipe.poe.PoeFlasks
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.asStateFlow
import kotlinx.coroutines.launch
import javax.inject.Inject

/**
 * Manages the lifecycle of all non-leader-key background macros.
 * Exposes [isEnabled] so the overlay can toggle all background macros on/off (see M3).
 */
class BackgroundMacroRunner @Inject constructor(
    private val triggerSkillMacro: TriggerSkillMacro,
    private val toggleAutoAttackMacro: ToggleAutoAttackMacro,
    private val triggerSkillsD4Macro: TriggerSkillsD4Macro,
    val autoFlaskMacro: AutoFlaskMacro,
    private val keyboardOutput: KeyboardOutput,
    private val tracker: BgMacroStatusTracker,
) {
    private val _isEnabled = MutableStateFlow(true)
    val isEnabled = _isEnabled.asStateFlow()

    /**
     * When true, background macro key output is suppressed.
     * Set by the Coordinator while the overlay picker is open, so that
     * macro-generated key presses don't reach the focused overlay window.
     */
    @Volatile
    var outputSuppressed = false

    val flaskSelectedConfig: StateFlow<PoeFlasks.Config>
        get() = autoFlaskMacro.selectedConfig

    val flaskAvailableConfigs: List<Pair<String, PoeFlasks.Config>>
        get() = autoFlaskMacro.availableConfigs

    val statusLines: StateFlow<List<BgMacroStatusLine>>
        get() = tracker.status

    fun toggle() {
        _isEnabled.value = !_isEnabled.value
    }

    fun selectFlaskConfig(config: PoeFlasks.Config) {
        autoFlaskMacro.selectConfig(config)
    }

    suspend fun run() {
        coroutineScope {
            // Periodically evict expired events so the status clears after 15s of inactivity
            launch {
                while (true) {
                    delay(1_000L)
                    tracker.tick()
                }
            }

            val suppress = { outputSuppressed }
            val flaskOutput = ReportingKeyboardOutput("flask", keyboardOutput, tracker, suppress)
            val focusOutput = ReportingKeyboardOutput("focus", keyboardOutput, tracker, suppress)
            val autoAtkOutput = ReportingKeyboardOutput("autoAtk", keyboardOutput, tracker, suppress)
            val d4SkillOutput = ReportingKeyboardOutput("d4Skill", keyboardOutput, tracker, suppress)

            // launch { triggerSkillMacro.run(isEnabled, focusOutput) }
            launch { toggleAutoAttackMacro.run(isEnabled, autoAtkOutput) }
            launch { triggerSkillsD4Macro.run(isEnabled, d4SkillOutput) }
            autoFlaskMacro.run(isEnabled, flaskOutput)
        }
    }
}
