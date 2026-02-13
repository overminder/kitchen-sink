package com.gh.om.ks.arpgmacro.app

import com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMaker
import com.gh.om.ks.arpgmacro.core.craft.dm.Poe2AugAnnulMagicItem
import com.gh.om.ks.arpgmacro.core.craft.dm.Poe2ChaosOnRare
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem.ExplicitMod.Matcher

object CraftPresets {
    /** Int-stacking cluster jewel: 4 of 6 target mods (ES, effect, int, AS, all res, attr). */
    val intStackCluster4 = CraftDecisionMaker.byDesiredMods(
        desiredModNames = listOf(
            "Glowing", "Powerful", "of the Prodigy",
            "of Mastery", "of the Kaleidoscope", "of the Meteor",
        ),
        desiredModCount = 4,
    )

    val poe2Frac = Poe2ChaosOnRare(
        Poe2ChaosOnRare.Args(
            listOf(
                // T1 Spirit
                "Countess'",
                // T1 Mana#
                "Ultramarine",
                // T1 Mana%
                "Mnemonic",
                // T1 ES%
                "Unassailable",
                // T1 Crit Damage
                "of Destruction",
                // T1 Crit Chance
                "of Unmaking",
            ).map(Matcher::byName),
            listOf(
                // T1 all res
                "of the Span",
                // T1 cast speed
                "of Legerdemain",
                // T1 Spell damage
                "Incanter's",
            ).map(Matcher::byName),
            2,
        )
    )

    val poe2Magic = Poe2AugAnnulMagicItem(
        Poe2AugAnnulMagicItem.Args(
            listOf(
                // T1 spell
                "Runic",
                // T1 cold level (+5)
                "of Frostbite",
            ).map(Matcher::byName),
            1,
        )
    )
}
