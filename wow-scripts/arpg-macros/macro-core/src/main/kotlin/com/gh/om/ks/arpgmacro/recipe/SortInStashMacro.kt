package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.MapScorerImpl
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.PoeItemParser
import com.gh.om.ks.arpgmacro.core.PoeScreenConstants
import com.gh.om.ks.arpgmacro.core.Screen
import com.gh.om.ks.arpgmacro.core.ScreenPoint
import com.gh.om.ks.arpgmacro.core.fmt
import com.gh.om.ks.arpgmacro.core.println
import javax.inject.Inject

class SortInStashMacro @Inject constructor(
    private val screen: Screen,
    private val poeInteractor: PoeInteractor,
    private val shouldContinueChecker: ShouldContinueChecker,
    private val consoleOutput: ConsoleOutput,
) : MacroDef {
    override suspend fun prepare(): MacroDef.Prepared {
        val shouldContinue = shouldContinueChecker.get(
            anyWindowTitles = GameTitles.ALL_POE,
        )

        return MacroDef.Prepared {
            if (!shouldContinue.value) return@Prepared
            val stashSlots = PoeScreenConstants.allGrids(
                start = PoeScreenConstants.firstItemInRegularStash,
                rows = 12,
                columns = 6,
                gridSize = PoeScreenConstants.bagGridSize,
            )
            val occupiedSlots = PoeScreenConstants.filterOccupiedSlots(
                stashSlots, screen.captureScreen(),
            )
            if (occupiedSlots.isEmpty()) {
                consoleOutput.println("No items found in stash")
                return@Prepared
            }
            doSort(
                shouldContinue = shouldContinue::value,
                inputs = occupiedSlots,
            )
        }
    }

    private suspend fun doSort(
        shouldContinue: () -> Boolean,
        inputs: List<ScreenPoint>,
    ) {
        val scorer = MapScorerImpl.SCARAB
        // Phase 1: Score all items
        val scoredItems = mutableListOf<Pair<ScreenPoint, Double>>()
        for (slot in inputs) {
            if (!shouldContinue()) return
            val text = poeInteractor.getItemDescriptionAt(slot) ?: ""
            val item = PoeItemParser.parseAsRollable(text)
            scoredItems += slot to scorer.evaluate(item).score
        }

        // Phase 2: Sort by score descending
        scoredItems.sortBy { -it.second }
        val scores = scoredItems.map { it.second.fmt() }
        val avg = scoredItems.map { it.second }.average().fmt()
        consoleOutput.println("${scoredItems.size} maps, avg score $avg, each: $scores")

        // Phase 3: Move all items to bag (Ctrl+click)
        for ((slot, _) in scoredItems) {
            if (!shouldContinue()) return
            poeInteractor.ctrlClick(slot)
        }

        // Phase 4: Move back from bag to stash in sorted order (Ctrl+Shift+click)
        val bagSlots = PoeScreenConstants.allGrids(
            start = PoeScreenConstants.firstItemInBag,
            rows = PoeScreenConstants.bagRows,
            columns = 10,
            gridSize = PoeScreenConstants.bagGridSize,
        ).take(inputs.size).toList()
        for (slot in bagSlots) {
            if (!shouldContinue()) return
            poeInteractor.ctrlShiftClick(slot)
        }
    }
}
