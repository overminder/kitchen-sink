package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMaker
import com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMakerV2
import com.gh.om.ks.arpgmacro.core.craft.CraftRerollProvider
import com.gh.om.ks.arpgmacro.core.craft.CraftRerollProviderV2
import com.gh.om.ks.arpgmacro.core.craft.CurrencySlots
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.MultiRollLoop
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.PoeScreenConstants
import com.gh.om.ks.arpgmacro.core.Screen
import com.gh.om.ks.arpgmacro.core.craft.asItemChecker
import com.gh.om.ks.arpgmacro.core.println
import com.gh.om.ks.arpgmacro.di.GameType
import javax.inject.Inject

class CraftRollingMacro @Inject constructor(
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
            val slots = poeInteractor.getOccupiedBagSlots()
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

class CraftRollingMacroV2 @Inject constructor(
    private val multiRollLoop: MultiRollLoop,
    private val shouldContinueChecker: ShouldContinueChecker,
    private val consoleOutput: ConsoleOutput,
    private val rerollProviderFactory: CraftRerollProviderV2.Factory,
    private val decisionMakerV2: CraftDecisionMakerV2,
    private val interactor: PoeInteractor,
) : MacroDef {
    override suspend fun prepare(): MacroDef.Prepared {
        val shouldContinue = shouldContinueChecker.get(
            anyWindowTitles = GameTitles.ALL_POE,
        )

        return MacroDef.Prepared {
            if (!shouldContinue.value) return@Prepared
            val slots = interactor.getOccupiedBagSlots()
            if (slots.isEmpty()) {
                consoleOutput.println("No items found in bag")
                return@Prepared
            }
            val dm = decisionMakerV2
            val reroll = rerollProviderFactory.create(10, dm)
            val report = multiRollLoop.rollItems(
                checker = dm.asItemChecker(),
                itemsToRoll = slots,
                rerollProvider = reroll,
                shouldContinue = shouldContinue::value,
            )
            consoleOutput.println(report.details)
        }
    }
}
