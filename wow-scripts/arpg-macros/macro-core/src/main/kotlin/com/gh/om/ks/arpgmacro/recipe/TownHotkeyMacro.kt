package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.postAsciiString
import com.gh.om.ks.arpgmacro.core.postPressRelease
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.stateIn
import javax.inject.Inject

class TownHotkeyMacro(
    private val deps: Deps,
    private val windowTitle: String,
    private val hotkeys: Map<String, String>,
) {

    suspend fun run() {
        val windowFlow = deps.activeWindowChecker.activeWindowFlow(setOf(windowTitle))
            .stateIn(CoroutineScope(currentCoroutineContext()))

        deps.keyboardInput.keyReleases().collect { key ->
            if (!windowFlow.value) return@collect
            val command = hotkeys[key] ?: return@collect
            deps.keyboardOutput.postPressRelease("Enter")
            deps.keyboardOutput.postAsciiString(command)
            deps.keyboardOutput.postPressRelease("Enter")
        }
    }

    class Deps @Inject constructor(
        val activeWindowChecker: ActiveWindowChecker,
        val keyboardInput: KeyboardInput,
        val keyboardOutput: KeyboardOutput,
    )

    class Factory @Inject constructor(
        private val deps: Deps,
    ) {
        fun create(
            windowTitle: String,
            hotkeys: Map<String, String>,
        ) = TownHotkeyMacro(deps, windowTitle, hotkeys)
    }
}
