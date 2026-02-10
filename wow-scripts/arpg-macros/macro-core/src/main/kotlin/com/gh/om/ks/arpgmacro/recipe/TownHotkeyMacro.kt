package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.postAsciiString
import com.gh.om.ks.arpgmacro.core.postPressRelease
import com.gh.om.ks.arpgmacro.di.GameType
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.stateIn
import javax.inject.Inject
import kotlin.text.get

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

private fun getHotKeys(gameType: GameType): Map<String, String> {
    return when (gameType) {
        GameType.POE1 -> mapOf(
            "F5" to "/hideout",
            "F6" to "/kingsmarch",
            "F7" to "/heist",
        )

        GameType.POE2 -> mapOf(
            "F5" to "/hideout",
        )

        GameType.Diablo3,
        GameType.Diablo4 -> emptyMap()
    }
}

class TownHotkeyMacroV2 @Inject constructor(
    private val activeWindowChecker: ActiveWindowChecker,
    private val keyboardInput: KeyboardInput,
    private val keyboardOutput: KeyboardOutput,
    private val gameType: GameType,
) {
    suspend fun run() {
        val windowFlow = activeWindowChecker.activeWindowFlow(setOf(GameTitles.from(gameType)))
            .stateIn(CoroutineScope(currentCoroutineContext()))

        val hotkeys = getHotKeys(gameType)

        // Not leader key based
        keyboardInput.keyReleases().collect { key ->
            if (!windowFlow.value) return@collect
            val command = hotkeys[key] ?: return@collect
            keyboardOutput.postPressRelease("Enter")
            keyboardOutput.postAsciiString(command)
            keyboardOutput.postPressRelease("Enter")
        }
    }
}
