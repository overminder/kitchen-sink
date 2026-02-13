package com.gh.om.ks.arpgmacro.core.craft

import com.gh.om.ks.arpgmacro.core.CheckResult
import com.gh.om.ks.arpgmacro.core.item.PoeCurrency
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem

fun interface CraftDecisionMakerV2 {
    fun getDecision(item: PoeRollableItem): Decision

    data class Decision(
        /**
         * A null type means done.
         * This doesn't need to be tiered -- the applier can switch the tier according to the available currencies.
         * Specifying a tiered means this roll is important and can benefit from a better tiered currency.
         */
        val type: PoeCurrency.KnownType?,
        val why: String,
        val bricked: Boolean = false,
    ) : CheckResult {
        val done: Boolean
            get() = type == null

        override val isGood: Boolean
            get() = done
    }
}

internal fun List<PoeRollableItem.ExplicitMod>.countOfMatches(
    matchers: List<PoeRollableItem.ExplicitMod.Matcher>
): Int {
    return count { mod ->
        matchers.anyMatches(mod)
    }
}

internal fun List<PoeRollableItem.ExplicitMod.Matcher>.anyMatches(mod: PoeRollableItem.ExplicitMod): Boolean {
    return any {
        it.matches(mod)
    }
}
