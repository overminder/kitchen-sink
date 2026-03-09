package com.gh.om.ks.arpgmacro.app

import com.gh.om.ks.arpgmacro.app.di.DaggerAppComponent
import com.gh.om.ks.arpgmacro.core.overlay.BackgroundMacroState
import com.gh.om.ks.arpgmacro.core.overlay.Coordinator
import com.gh.om.ks.arpgmacro.core.overlay.LeaderKeyListener
import com.gh.om.ks.arpgmacro.di.GameType
import com.gh.om.ks.arpgmacro.recipe.GameTitles
import com.github.kwhat.jnativehook.GlobalScreen
import kotlinx.coroutines.Job
import kotlinx.coroutines.launch
import kotlinx.coroutines.async
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.runBlocking

fun main() {
    if (!isDebugging()) {
        GlobalScreen.registerNativeHook()
    } else {
        println("WARNING: debugging with JNativeHook makes mouse unusable")
    }
    try {
        val component = DaggerAppComponent.create()

        // Build macro infrastructure
        val macroDefs = GameType.entries.associateWith { gameType ->
            component.gameSubcomponentFactory.create(gameType).macroDefs()
        }
        val macroRegistry = MacroRegistryImpl()
        val macroRunner = MacroRunnerImpl(macroDefs)
        val focusManager = component.focusManager()
        val overlayController = component.overlayController()

        // Start the overlay window (hidden initially)
        overlayController.start()
        // Exclude the overlay from GDI screen captures so macros don't see it in pixel reads
        focusManager.excludeWindowFromCapture(overlayController.overlayWindowTitle())

        // Wire background macros into the overlay picker (M3.1)
        val backgroundMacroRunner = component.backgroundMacroRunner()
        overlayController.connectBackgroundMacros(
            BackgroundMacroState(
                isEnabled = backgroundMacroRunner.isEnabled,
                onToggle = backgroundMacroRunner::toggle,
                availableFlaskConfigs = backgroundMacroRunner.flaskAvailableConfigs,
                selectedFlaskConfig = backgroundMacroRunner.flaskSelectedConfig,
                onSelectFlaskConfig = backgroundMacroRunner::selectFlaskConfig,
                statusLines = backgroundMacroRunner.statusLines,
                gameTitles = GameType.entries.map { GameTitles.from(it) }.toSet(),
            )
        )

        val coordinator = Coordinator(
            focusManager = focusManager,
            overlayController = overlayController,
            macroRegistry = macroRegistry,
            macroRunner = macroRunner,
        )

        // Simplified leader key listener (just detects Alt+X, no command parsing)
        val leaderKeyListener = LeaderKeyListener(
            leaderChord = setOf("Alt", "X"),
            keyboardInput = component.keyboardInput(),
        )

        println("Launching macros (Alt+X opens overlay, F4 to stop running macro)")
        println("Registered macros:")
        for (reg in macroRegistry.allMacros()) {
            val filter = if (reg.gameFilter.isEmpty()) "Any" else reg.gameFilter.joinToString("/")
            println("  ${reg.name} [$filter]")
        }

        val jobs = mutableListOf<Job>()
        runBlocking {
            // Leader key → coordinator
            // Each leader key event launches independently so the flow collector
            // isn't blocked by onLeaderKey() suspending on awaitSelection/macro execution.
            // The coordinator's volatile state checks handle concurrent calls safely.
            jobs += async {
                leaderKeyListener.leaderKeyEvents().collect {
                    launch { coordinator.onLeaderKey() }
                }
            }

            // Background macros (triggerSkill, toggleAutoAttack, D4 skills)
            jobs += async { backgroundMacroRunner.run() }

            // Non-leader key based macros (town hotkey)
            GameType.entries.forEach { gameType ->
                val townHotkeyMacro = component.gameSubcomponentFactory
                    .create(gameType)
                    .macroDefs()
                    .townHotkeyMacro
                jobs += async { townHotkeyMacro.run() }
            }

            jobs.joinAll()
        }
    } finally {
        GlobalScreen.unregisterNativeHook()
    }
}
