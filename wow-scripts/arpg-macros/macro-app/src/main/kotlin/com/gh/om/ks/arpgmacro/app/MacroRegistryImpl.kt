package com.gh.om.ks.arpgmacro.app

import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.overlay.ActivationContext
import com.gh.om.ks.arpgmacro.core.overlay.MacroRegistration
import com.gh.om.ks.arpgmacro.core.overlay.MacroRegistry
import com.gh.om.ks.arpgmacro.core.overlay.MacroRunner
import com.gh.om.ks.arpgmacro.di.GameType
import com.gh.om.ks.arpgmacro.recipe.GameTitles
import com.gh.om.ks.arpgmacro.recipe.MacroDefsComponent

/**
 * Defines the mapping from macro registrations to actual macro implementations.
 * This is the v3 replacement for the old `macroMapping` list + `WhichGame` + trigger keys.
 */
data class MacroSpec(
    val id: String,
    val name: String,
    val category: String,
    val description: String = "",
    val whichGame: WhichGame,
    val whichMacro: (MacroDefsComponent) -> MacroDef,
)

sealed class WhichGame {
    data class Each(val games: List<GameType>) : WhichGame()
    data object Any : WhichGame()

    fun toGameFilter(): Set<String> = when (this) {
        Any -> emptySet()
        is Each -> games.map { it.name }.toSet()
    }

    companion object {
        val POE1 = Each(listOf(GameType.POE1))
        val POE2 = Each(listOf(GameType.POE2))
        val EACH_POE = Each(listOf(GameType.POE1, GameType.POE2))
    }
}

val macroSpecs = listOf(
    MacroSpec("map-rolling", "Map rolling", "Crafting", whichGame = WhichGame.EACH_POE) { it.mapRolling },
    MacroSpec("craft-rolling-v2", "Craft rolling (v2)", "Crafting", whichGame = WhichGame.POE2) { it.craftRollingV2 },
    MacroSpec("tablet-rolling", "Tablet rolling", "Crafting",
        description = "Chaos spam on tablets. Target: Abyss groups with specific good mods.",
        whichGame = WhichGame.POE2) { it.tabletRollingMacro },
    MacroSpec("craft-rolling", "Craft rolling", "Crafting", whichGame = WhichGame.EACH_POE) { it.craftRolling },
    MacroSpec("sort-stash", "Sort in stash", "Utility", whichGame = WhichGame.EACH_POE) { it.sortInStash },
    MacroSpec("print-mouse-pos", "Print mouse pos", "Utility", whichGame = WhichGame.Any) { it.printMousePos },
    MacroSpec("parse-print-item", "Parse & print item", "Utility", whichGame = WhichGame.Any) { it.parseAndPrintItem },
    MacroSpec("dump-bag", "Dump bag to stash", "Utility",
        description = "Ctrl+click all occupied bag slots to stash.",
        whichGame = WhichGame.POE1) { it.dumpBagToStash },
    MacroSpec("dump-bag-forced", "Force dump bag to stash", "Utility",
        description = "Ctrl+Shift+click all occupied bag slots to current stash tab.",
        whichGame = WhichGame.POE1) { it.dumpBagToStashForced },
    MacroSpec("ctrl-click-cursor", "Ctrl-click at cursor (×300)", "Utility",
        description = "Ctrl+click 300 times at the cursor position captured on activation.",
        whichGame = WhichGame.POE1) { it.ctrlClickAtCursor },
)

/**
 * Implementation of [MacroRegistry] backed by the static [macroSpecs] list.
 */
class MacroRegistryImpl : MacroRegistry {
    private val registrations = macroSpecs.map { spec ->
        MacroRegistration(
            id = spec.id,
            name = spec.name,
            category = spec.category,
            description = spec.description,
            gameFilter = spec.whichGame.toGameFilter(),
        )
    }

    override fun allMacros(): List<MacroRegistration> = registrations

    override fun macrosFor(context: ActivationContext): List<MacroRegistration> {
        // Only show macros when in a recognized game — avoids interrupting other workflows
        val detectedGame = GameType.entries.find { GameTitles.from(it) == context.gameTitle }
            ?: return emptyList()
        return registrations.filter { reg ->
            reg.gameFilter.isEmpty() || detectedGame.name in reg.gameFilter
        }
    }
}

/**
 * Implementation of [MacroRunner] that resolves macro specs to actual MacroDef instances
 * and runs them.
 */
class MacroRunnerImpl(
    private val macroDefs: Map<GameType, MacroDefsComponent>,
) : MacroRunner {
    private val specById = macroSpecs.associateBy { it.id }

    override suspend fun run(registration: MacroRegistration, context: ActivationContext) {
        val spec = specById[registration.id]
            ?: error("Unknown macro id: ${registration.id}")

        val gameTypes = when (val wg = spec.whichGame) {
            WhichGame.Any -> listOf(GameType.POE1)
            is WhichGame.Each -> wg.games
        }

        // Detect which game is actually running from the activation context
        val detectedGame = GameType.entries.find { GameTitles.from(it) == context.gameTitle }
        val targetGameTypes = if (detectedGame != null && detectedGame in gameTypes) {
            listOf(detectedGame)
        } else {
            // Fallback: run for first available
            listOf(gameTypes.first())
        }

        for (gameType in targetGameTypes) {
            val defs = macroDefs[gameType] ?: continue
            val macroDef = spec.whichMacro(defs)
            val prepared = macroDef.prepare()
            prepared.run(context)
        }
    }
}
