package com.gh.om.ks.arpgmacro.core.craft.dm

import com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMakerV2
import com.gh.om.ks.arpgmacro.core.craft.anyMatches
import com.gh.om.ks.arpgmacro.core.craft.countOfMatches
import com.gh.om.ks.arpgmacro.core.item.PoeCurrency
import com.gh.om.ks.arpgmacro.core.item.PoeItem
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem

/**
 * Somewhat similar to [Poe2ChaosOnRare], but:
 * - Only do exalt + chaos. Don't use annul.
 * - The input is a list of "groups". Each group is a (list of good mods, desired mod count).
 *   As long as any group is matched, the item is considered good.
 *   See [com.gh.om.ks.arpgmacro.recipe.TabletMods.abyssGroup1] and 2 for example groups.
 */
class Poe2ChaoOnTablet(
    private val args: Args,
) : CraftDecisionMakerV2 {
    override fun getDecision(item: PoeRollableItem): CraftDecisionMakerV2.Decision {
        require(item.klass == PoeItem.ConstKlass.Tablet) {
            "Expecting tablet, got $item"
        }

        val mods = item.explicitMods

        // Check if any group is already satisfied
        for (group in args.groups) {
            val matchCount = mods.countOfMatches(group.goodMods)
            if (matchCount >= group.goodModCount && !group.hasViolation(mods)) {
                return CraftDecisionMakerV2.Decision(null, "Group satisfied: $matchCount >= ${group.goodModCount}")
            }
        }

        // Find if any group has a clean path (all current mods are good for that group, no violations)
        for (group in args.groups) {
            val matchCount = mods.countOfMatches(group.goodMods)
            val badCount = mods.size - matchCount
            if (matchCount > 0 && badCount == 0 && !group.hasViolation(mods)) {
                return CraftDecisionMakerV2.Decision(
                    args.exaltType,
                    "Group has $matchCount good mod(s), 0 bad, exalting"
                )
            }
        }

        // No group has a clean path, chaos to reroll
        return CraftDecisionMakerV2.Decision(PoeCurrency.Companion.Chaos, "No clean group, chaos")
    }

    operator fun plus(other: Poe2ChaoOnTablet): Poe2ChaoOnTablet {
        return Poe2ChaoOnTablet(args + other.args)
    }

    companion object {
        /** Checks if a group's negative/mustHave constraints are violated. */
        private fun Group.hasViolation(mods: List<PoeRollableItem.ExplicitMod>): Boolean {
            val hasNegative = badMods.isNotEmpty() && mods.any { badMods.anyMatches(it) }
            val mustHaveMet = mustHaveMods.isEmpty() || mods.countOfMatches(mustHaveMods) >= mustHaveCount
            return hasNegative || !mustHaveMet
        }
    }

    data class Group(
        val goodMods: List<PoeRollableItem.ExplicitMod.Matcher>,
        val goodModCount: Int,
        /** Mods that must NOT be present on the final item. Chaos if any match. */
        val badMods: List<PoeRollableItem.ExplicitMod.Matcher> = emptyList(),
        /** Mods that must be present on the final item. Chaos if fewer than [mustHaveCount] match. */
        val mustHaveMods: List<PoeRollableItem.ExplicitMod.Matcher> = emptyList(),
        val mustHaveCount: Int = mustHaveMods.size,
    ) {
        init {
            require(goodMods.isNotEmpty())
            require(goodModCount >= 1)
            require(goodMods.size >= goodModCount)
            // Tablets can only have 4 mods.
            require(goodModCount <= 4)
            require(mustHaveCount <= mustHaveMods.size)
        }
    }

    class Args(
        val groups: List<Group>,
        val exaltType: PoeCurrency.TieredType = PoeCurrency.Exalt.asGreater(),
    ) {
        init {
            require(groups.isNotEmpty())
            require(exaltType.kind == PoeCurrency.CanHaveTier.Exalt)
        }

        operator fun plus(other: Args): Args {
            require(exaltType == other.exaltType)
            return Args(groups + other.groups, exaltType)
        }
    }
}