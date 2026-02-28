package com.gh.om.ks.arpgmacro.recipe

import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.flow.MutableStateFlow
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
) {
    private val _isEnabled = MutableStateFlow(true)
    val isEnabled = _isEnabled.asStateFlow()

    fun toggle() {
        _isEnabled.value = !_isEnabled.value
    }

    suspend fun run() {
        coroutineScope {
            launch { triggerSkillMacro.run(isEnabled) }
            launch { toggleAutoAttackMacro.run(isEnabled) }
            triggerSkillsD4Macro.run(isEnabled)
        }
    }
}
