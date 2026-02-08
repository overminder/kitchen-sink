package com.gh.om.ks.arpgmacro.app

import com.gh.om.ks.arpgmacro.core.CraftDecisionMaker

object CraftPresets {
    /** Int-stacking cluster jewel: 4 of 6 target mods (ES, effect, int, AS, all res, attr). */
    val intStackCluster4 = CraftDecisionMaker.byDesiredMods(
        desiredModNames = listOf(
            "Glowing", "Powerful", "of the Prodigy",
            "of Mastery", "of the Kaleidoscope", "of the Meteor",
        ),
        desiredModCount = 4,
    )
}
