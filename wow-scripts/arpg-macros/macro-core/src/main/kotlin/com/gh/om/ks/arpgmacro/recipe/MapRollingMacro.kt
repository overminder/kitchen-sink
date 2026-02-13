package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.*
import com.gh.om.ks.arpgmacro.core.craft.ChaosOrAlchMapRerollProvider
import com.gh.om.ks.arpgmacro.core.craft.ChaosRerollProvider
import com.gh.om.ks.arpgmacro.core.craft.CurrencySlots
import com.gh.om.ks.arpgmacro.core.craft.ScourAlchRerollProvider
import com.gh.om.ks.arpgmacro.core.map.MapScorerImpl
import com.gh.om.ks.arpgmacro.di.GameType
import javax.inject.Inject

class MapRollingMacro @Inject constructor(
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
            val slots = poeInteractor.getOccupiedBagSlots()
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
