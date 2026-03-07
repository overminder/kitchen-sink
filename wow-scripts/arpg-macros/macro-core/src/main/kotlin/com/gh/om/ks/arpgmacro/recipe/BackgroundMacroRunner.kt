package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.recipe.poe.PoeFlasks
import kotlinx.coroutines.coroutineScope
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
) {
    private val _isEnabled = MutableStateFlow(true)
    val isEnabled = _isEnabled.asStateFlow()

    val flaskSelectedConfig: StateFlow<PoeFlasks.Config>
        get() = autoFlaskMacro.selectedConfig

    val flaskAvailableConfigs: List<Pair<String, PoeFlasks.Config>>
        get() = autoFlaskMacro.availableConfigs

    fun toggle() {
        _isEnabled.value = !_isEnabled.value
    }

    fun selectFlaskConfig(config: PoeFlasks.Config) {
        autoFlaskMacro.selectConfig(config)
    }

    suspend fun run() {
        coroutineScope {
            // Don't toggle for now.
            // launch { triggerSkillMacro.run(isEnabled) }
            // launch { toggleAutoAttackMacro.run(isEnabled) }
            // launch { triggerSkillsD4Macro.run(isEnabled) }
            autoFlaskMacro.run(isEnabled)
        }
    }
}
