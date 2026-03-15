package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.Screen
import com.gh.om.ks.arpgmacro.core.buff.BuffManager
import com.gh.om.ks.arpgmacro.di.GameType
import com.gh.om.ks.arpgmacro.recipe.poe.PoeFlasks
import kotlinx.coroutines.async
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.asStateFlow
import kotlinx.coroutines.flow.collectLatest
import kotlinx.coroutines.flow.combine
import kotlinx.coroutines.flow.stateIn
import java.time.Instant
import javax.inject.Inject
import kotlin.time.Duration.Companion.milliseconds

/**
 * Background macro for POE1: auto-uses flasks while W is held.
 * Config can be changed at runtime via the overlay dropdown.
 *
 * Ports [GameSpecific.autoFlaskInPoe].
 */
class AutoFlaskMacro @Inject constructor(
    private val keyboardInput: KeyboardInput,
    private val keyboardOutput: KeyboardOutput,
    private val activeWindowChecker: ActiveWindowChecker,
    private val screen: Screen,
    private val clock: Clock,
) {
    private val _selectedConfig: MutableStateFlow<PoeFlasks.Config> = MutableStateFlow(PoeFlasks.mbTincture)
    val selectedConfig: StateFlow<PoeFlasks.Config> = _selectedConfig.asStateFlow()
    val availableConfigs: List<Pair<String, PoeFlasks.Config>> = PoeFlasks.allConfigs

    fun selectConfig(config: PoeFlasks.Config) {
        _selectedConfig.value = config
    }

    suspend fun run(isEnabled: StateFlow<Boolean>, keyboardOutput: KeyboardOutput = this.keyboardOutput) {
        coroutineScope {
            val isPoe = activeWindowChecker.activeWindowFlow(setOf(GameTitles.from(GameType.POE1)))
                .stateIn(this)
            val triggerEnabled = keyboardInput.triggerKeyEnabledFlow(setOf("F4", "F5", "F6", "F7"))
                .stateIn(this)

            fun active() = isEnabled.value && isPoe.value && triggerEnabled.value

            val skillKeys = setOf("W")

            // React to config changes by recreating the BuffManager
            _selectedConfig.collectLatest { config ->
                val keeper = config.toKeeper(screen, keyboardOutput, clock)
                val fm = BuffManager(clock, keeper)

                // Inner coroutineScope so all async children are cancelled when
                // collectLatest moves to a new config value.
                coroutineScope {
                    val flaskInputs = combine(
                        isPoe, keyboardInput.keyStates()
                    ) { poeActive, keyState ->
                        PoeFlasks.InputEvent(
                            timestamp = Instant.ofEpochMilli(clock.currentTimeMillis()),
                            shouldUse = poeActive && skillKeys.any(keyState::contains),
                        )
                    }

                    val flaskInputState = flaskInputs.stateIn(this)

                    async { PoeFlasks.runGapFixer(fm, flaskInputs) { isPoe.value && isEnabled.value } }

                    async {
                        keyboardInput.keyPresses().collect { key ->
                            if (key in skillKeys) {
                                val a = active()
                                if (a) fm.useAll()
                            }
                        }
                    }

                    async {
                        while (true) {
                            if (flaskInputState.value.shouldUse && active()) {
                                fm.useAll()
                            }
                            clock.delay(100.milliseconds)
                        }
                    }
                }
            }
        }
    }
}
