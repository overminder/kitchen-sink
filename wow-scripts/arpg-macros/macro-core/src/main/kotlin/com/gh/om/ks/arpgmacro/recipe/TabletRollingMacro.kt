package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.MultiRollLoop
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.arrange.Poe2SortTablet
import com.gh.om.ks.arpgmacro.core.craft.CraftRerollProviderV2
import com.gh.om.ks.arpgmacro.core.craft.asItemChecker
import com.gh.om.ks.arpgmacro.core.craft.dm.Poe2ChaoOnTablet
import com.gh.om.ks.arpgmacro.core.craft.dm.Poe2TabletFirstPass
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem.ExplicitMod.Matcher
import com.gh.om.ks.arpgmacro.core.println
import com.gh.om.ks.arpgmacro.recipe.TabletMods.Abyss
import javax.inject.Inject

object TabletMods {
    val eff = "Challenger's"
    val rarePack = "Brimming"

    object Abyss {
        private val additionalRares = "of Champions"
        private val abyssalMods = "of Dark Power"

        // Double chance for abyss pits to have rewards
        private val pitRewards = "of Treasures"

        // Desecrated currencies
        private val bones = "of Ossification"

        private val moreDifficult = "of Escalation"

        val omenFarm = listOf(
            eff, rarePack, Abyss.additionalRares, Abyss.abyssalMods
        ).map(Matcher::byName)
        val omenFarmMustHave = listOf(
            Abyss.abyssalMods
        ).map(Matcher::byName)

        val desecrateCurrencyFarm = listOf(
            Abyss.pitRewards, Abyss.bones,
        ).map(Matcher::byName)

        val negatives = listOf(Abyss.moreDifficult).map(Matcher::byName)
    }

    object Ritual {
        private val pack = "Breeding"
        private val magicPack = "Teeming"

        private val moreReroll = "of Prayers"

        private val incTribute = "of Sacrifice"
        private val rerollCost = "of the Dogma"
        private val deferCost = "of Devotion"
        private val reviveMagic = "of the Foundling"
        private val omen = "of Omens"

        val moreRerollOnly = listOf(Matcher.byName(moreReroll))
        val moreRerollLuxury = listOf(
            moreReroll,
            rerollCost,
            deferCost,
            omen,
        ).map(Matcher::byName)
        val everything = listOf(
            pack,
            magicPack,
            moreReroll,
            incTribute,
            rerollCost,
            deferCost,
            reviveMagic,
            omen,
        ).map(Matcher::byName)
        val oneOfCost = listOf(
            rerollCost,
            deferCost,
        ).map(Matcher::byName)
    }

}

object TabletPresets {
    val abyssCheap = Poe2TabletFirstPass(
        Poe2TabletFirstPass.Args(
            Abyss.omenFarm + Abyss.desecrateCurrencyFarm
        )
    )
    val abyssViaChaos = Poe2ChaoOnTablet(
        Poe2ChaoOnTablet.Args(
            listOf(
                Poe2ChaoOnTablet.Group(
                    goodMods = Abyss.omenFarm,
                    goodModCount = 3,
                    mustHaveMods = Abyss.omenFarmMustHave,
                    badMods = Abyss.negatives,
                ),
                Poe2ChaoOnTablet.Group(
                    goodMods = Abyss.desecrateCurrencyFarm,
                    goodModCount = 2,
                    badMods = Abyss.negatives,
                ),
            )
        )
    )

    val ritual = Poe2ChaoOnTablet(
        Poe2ChaoOnTablet.Args(
            listOf(
                Poe2ChaoOnTablet.Group(
                    goodMods = TabletMods.Ritual.moreRerollOnly,
                    goodModCount = 1,
                ),
                Poe2ChaoOnTablet.Group(
                    goodMods = TabletMods.Ritual.oneOfCost,
                    goodModCount = 2,
                ),
                Poe2ChaoOnTablet.Group(
                    goodMods = TabletMods.Ritual.everything,
                    // Could be too strict. Intention: The above 2 (reroll, cost) cover all usages.
                    // This 3rd group is just fishing for extra.
                    goodModCount = 4,
                    mustHaveMods = TabletMods.Ritual.moreRerollLuxury,
                    mustHaveCount = 1,
                ),
            )
        )
    )

    val ALL = abyssViaChaos + ritual
}

class TabletRollingMacro @Inject constructor(
    private val multiRollLoop: MultiRollLoop,
    private val sorterFactory: Poe2SortTablet.Factory,
    private val shouldContinueChecker: ShouldContinueChecker,
    private val interactor: PoeInteractor,
    private val rerollFactory: CraftRerollProviderV2.Factory,
    private val consoleOutput: ConsoleOutput,
) : MacroDef {
    override suspend fun prepare(): MacroDef.Prepared {
        val dm = TabletPresets.ALL
        val shouldContinue = shouldContinueChecker.getV2()

        suspend fun run() {
            if (!shouldContinue.value) {
                return
            }
            val reroll = rerollFactory.create(500, dm)
            val slots = interactor.getOccupiedBagSlots()
            val report = multiRollLoop.rollItems(
                dm.asItemChecker(),
                slots,
                reroll,
                shouldContinue::value,
            )
            consoleOutput.println(report.details)
        }

        return MacroDef.Prepared(::run)
    }
}
