package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.CraftDecisionMaker
import com.gh.om.ks.arpgmacro.core.CraftRerollProvider
import com.gh.om.ks.arpgmacro.core.CurrencySlots
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.MultiRollLoop
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.PoeScreenConstants
import com.gh.om.ks.arpgmacro.core.Screen
import com.gh.om.ks.arpgmacro.core.asItemChecker
import com.gh.om.ks.arpgmacro.core.println
import javax.inject.Inject

class CraftRollingMacro @Inject constructor(
    private val screen: Screen,
    private val poeInteractor: PoeInteractor,
    private val multiRollLoop: MultiRollLoop,
    private val shouldContinueChecker: ShouldContinueChecker,
    private val consoleOutput: ConsoleOutput,
    private val currencySlots: CurrencySlots,
    private val clock: Clock,
    private val craftDecisionMaker: CraftDecisionMaker,
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
                    columns = 10,
                    gridSize = PoeScreenConstants.bagGridSize,
                ),
                screen.captureScreen(),
            )
            if (slots.isEmpty()) {
                consoleOutput.println("No items found in bag")
                return@Prepared
            }
            val reroll = CraftRerollProvider(
                fuel = 5000,
                dm = craftDecisionMaker,
                interactor = poeInteractor,
                currencySlots = currencySlots,
                clock = clock,
            )
            val report = multiRollLoop.rollItems(
                checker = craftDecisionMaker.asItemChecker(),
                itemsToRoll = slots,
                rerollProvider = reroll,
                shouldContinue = shouldContinue::value,
            )
            consoleOutput.println(report.details)
        }
    }
}
