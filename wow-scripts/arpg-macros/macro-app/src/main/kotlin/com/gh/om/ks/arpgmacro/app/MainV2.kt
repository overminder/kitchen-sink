package com.gh.om.ks.arpgmacro.app

import com.gh.om.ks.arpgmacro.app.di.AppComponent
import com.gh.om.ks.arpgmacro.app.di.DaggerAppComponent
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.overlay.OverlayEntry
import com.gh.om.ks.arpgmacro.di.GameType
import com.gh.om.ks.arpgmacro.recipe.MacroDefsComponent
import com.github.kwhat.jnativehook.GlobalScreen
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Job
import kotlinx.coroutines.async
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.runBlocking

private data class MacroMapping(
    val triggerKey: String,
    val displayName: String,
    val category: String,
    val whichGame: WhichGame,
    val whichMacro: (MacroDefsComponent) -> MacroDef,
)

private sealed class WhichGame {
    data class Each(val games: List<GameType>) : WhichGame()
    data object Any : WhichGame()

    companion object {
        val POE1 = WhichGame.Each(listOf(GameType.POE1))
        val POE2 = WhichGame.Each(listOf(GameType.POE2))
        val EACH_POE = WhichGame.Each(listOf(GameType.POE1, GameType.POE2))
    }
}

// This makes it clear which macro is triggered by which key, on which game.
// XXX macros usually know which game they support. Why not ask them?
private val macroMapping = listOf(
    MacroMapping("02", "Print mouse pos", "Utility", WhichGame.Any) { it.printMousePos },
    MacroMapping("021", "Parse & print item", "Utility", WhichGame.Any) { it.parseAndPrintItem },
    MacroMapping("11", "Map rolling", "Crafting", WhichGame.EACH_POE) { it.mapRolling },
    MacroMapping("12", "Craft rolling (v2)", "Crafting", WhichGame.POE2) { it.craftRollingV2 },
    MacroMapping("13", "Tablet rolling", "Crafting", WhichGame.POE2) { it.tabletRollingMacro },
    MacroMapping("14", "Sort in stash", "Utility", WhichGame.EACH_POE) { it.sortInStash },
    MacroMapping("15", "Craft rolling", "Crafting", WhichGame.EACH_POE) { it.craftRolling },
)

private fun CoroutineScope.instantiateMacrosAndTriggers(
    component: AppComponent,
    outJobs: MutableList<Job>
) {
    val mdefss = GameType.entries.associateWith { gameType ->
        component.gameSubcomponentFactory.create(gameType).macroDefs()
    }

    for (mmap in macroMapping) {
        val gameTypes = when (val wg = mmap.whichGame) {
            // Use a random game type.
            WhichGame.Any -> listOf(GameType.POE1)
            is WhichGame.Each -> wg.games
        }

        val macros = gameTypes.map { gameType ->
            val mdef = requireNotNull(mdefss[gameType]) {
                "Didn't find $gameType's macro whose key is ${mmap.triggerKey}"
            }
            mmap.whichMacro(mdef)
        }

        val m = macros.first()
        println("  ${mmap.whichGame} ${m.javaClass.simpleName}:      Alt+X, ${mmap.triggerKey}")

        outJobs += async {
            val prepared = macros.map {
                it.prepare()
            }
            component.leaderKeyDetector().isEnabled(mmap.triggerKey).collect { enabled ->
                if (enabled) {
                    prepared.forEach {
                        // Each macro is expected to check their own game's actual running status.
                        it.run()
                    }
                }
            }
        }
    }
}

internal val overlayEntries = macroMapping.map { mmap ->
    OverlayEntry(
        key = mmap.triggerKey,
        label = mmap.displayName,
        category = mmap.category,
    )
}

fun main() {
    if (!isDebugging()) {
        GlobalScreen.registerNativeHook()
    } else {
        println("WARNING: debugging with JNativeHook makes mouse unusable")
    }
    try {
        val component = DaggerAppComponent.create()

        // Start the overlay window (hidden initially)
        component.overlayOutputImpl().start()
        println("compose.start ${component.overlayOutputImpl()}")

        println("Launching macros (Alt+X leader key, F4 to stop)")
        val jobs = mutableListOf<Job>()
        runBlocking {
            instantiateMacrosAndTriggers(component, jobs)

            // Non-leader key based
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
