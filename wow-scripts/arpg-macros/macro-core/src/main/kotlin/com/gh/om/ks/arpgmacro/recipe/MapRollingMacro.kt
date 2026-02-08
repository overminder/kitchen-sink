package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ChaosOrAlchMapRerollProvider
import com.gh.om.ks.arpgmacro.core.ChaosRerollProvider
import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.CurrencySlots
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.MapScorerImpl
import com.gh.om.ks.arpgmacro.core.MultiRollLoop
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.PoeScreenConstants
import com.gh.om.ks.arpgmacro.core.ScourAlchRerollProvider
import com.gh.om.ks.arpgmacro.core.Screen
import com.gh.om.ks.arpgmacro.core.println
import javax.inject.Inject

class MapRollingMacro @Inject constructor(
    private val screen: Screen,
    private val poeInteractor: PoeInteractor,
    private val multiRollLoop: MultiRollLoop,
    private val shouldContinueChecker: ShouldContinueChecker,
    private val consoleOutput: ConsoleOutput,
    private val currencySlots: CurrencySlots,
) : MacroDef {
    override suspend fun prepare(): MacroDef.Prepared {
        val shouldContinue = shouldContinueChecker.get(
            anyWindowTitles = GameTitles.ALL_POE,
        )

        return MacroDef.Prepared {
            if (!shouldContinue.value) return@Prepared
            val slots = PoeScreenConstants.filterOccupiedSlots(
                PoeScreenConstants.allGrids(
                    start = PoeScreenConstants.firstItemInBag,
                    rows = PoeScreenConstants.bagRows,
                    columns = PoeScreenConstants.bagColumns,
                    gridSize = PoeScreenConstants.bagGridSize,
                ),
                screen.captureScreen(),
            )
            if (slots.isEmpty()) {
                consoleOutput.println("No items found in bag")
                return@Prepared
            }
            val reroll = ChaosOrAlchMapRerollProvider(
                chaos = ChaosRerollProvider(
                    fuel = 500,
                    interactor = poeInteractor,
                    chaosSlot = currencySlots.chaos,
                    scourSlot = currencySlots.scour,
                    alchSlot = currencySlots.alch,
                ),
                alch = ScourAlchRerollProvider(
                    fuel = 500,
                    interactor = poeInteractor,
                    scourSlot = currencySlots.scour,
                    alchSlot = currencySlots.alch,
                ),
            )
            val report = multiRollLoop.rollItems(
                checker = MapScorerItemChecker(MapScorerImpl.SCARAB_OR_MAP),
                itemsToRoll = slots,
                rerollProvider = reroll,
                shouldContinue = shouldContinue::value,
            )
            consoleOutput.println(report.details)
        }
    }
}
