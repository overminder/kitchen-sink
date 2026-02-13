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
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem.ExplicitMod.Matcher
import com.gh.om.ks.arpgmacro.core.println
import javax.inject.Inject

object TabletMods {
    val eff = "Challenger's"
    val rarePack = "Brimming"

    object Abyss {
        val additionalRares = "of Champions"
        val abyssalMods = "of Dark Power"

        // Double chance for abyss pits to have rewards
        val pitRewards = "of Treasures"
        // Desecrated currencies
        val bones = "of Ossification"

        val moreDifficult = "of Escalation"
    }

    // For omen farming (more rares + abyssal mods + IIQ)
    // 3 is good enough.
    val abyssGroup1 = listOf(
        eff, rarePack, Abyss.additionalRares, Abyss.abyssalMods
    ).map(Matcher::byName)
    val abyssGroup1MustHave = listOf(
        Abyss.abyssalMods
    ).map(Matcher::byName)

    // For desecrated currency farming
    val abyssGroup2 = listOf(
        Abyss.pitRewards, Abyss.bones,
    ).map(Matcher::byName)

    val abyssNegative = listOf(Abyss.moreDifficult).map(Matcher::byName)
}

object TabletPresets {
    val abyssCheap = Poe2TabletFirstPass(
        Poe2TabletFirstPass.Args(
            TabletMods.abyssGroup1 + TabletMods.abyssGroup2
        )
    )
    val abyssViaChaos = Poe2ChaoOnTablet(
        Poe2ChaoOnTablet.Args(
            listOf(
                Poe2ChaoOnTablet.Group(
                    goodMods = TabletMods.abyssGroup1,
                    goodModCount = 3,
                    mustHaveMods = TabletMods.abyssGroup1MustHave,
                    badMods = TabletMods.abyssNegative,
                ),
                Poe2ChaoOnTablet.Group(
                    goodMods = TabletMods.abyssGroup2,
                    2,
                    TabletMods.abyssNegative,
                ),
            )
        )
    )
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
        val dm = TabletPresets.abyssViaChaos
        val shouldContinue = shouldContinueChecker.getV2()

        suspend fun run() {
            if (!shouldContinue.value) {
                return
            }
            val reroll = rerollFactory.create(200, dm)
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
