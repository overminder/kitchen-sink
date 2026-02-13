package com.gh.om.ks.arpgmacro.core.craft.dm

import com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMakerV2
import com.gh.om.ks.arpgmacro.core.craft.countOfMatches
import com.gh.om.ks.arpgmacro.core.item.PoeCurrency
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem

/**
 * In POE2, crafting on a rare item is similar to alt-aug-regal-exalt crafting on cluster in POE1.
 * POE2 0.4 temple's produces tons of chaos, annul, and perfect exalt for this kind of crafting.
 *
 * This can either roll a non-fractured or a fractured rare item (fractured mod can't be changed / removed).
 * To be considered "done", an item needs:
 * - 0 or 1 fractured mod (precondition)
 * - At least one HP mod (matched by [Args.highPriorityMods])
 * - At least [Args.desiredModCount] good mods (both HP or LP aka [Args.lowPriorityMods]) are good.
 * For rolling efficiency's purpose, we avoid adding new mods when any of the mods are bad. However, we allow
 * the end item to have bad mods that initially came from somewhere else.
 */
class Poe2ChaosOnRare(
    val args: Args,
) : CraftDecisionMakerV2 {
    override fun getDecision(item: PoeRollableItem): CraftDecisionMakerV2.Decision {
        val nonFracturedMods = item.explicitMods.filterNot { it.fractured }
        val hpCount = nonFracturedMods.countOfMatches(args.highPriorityMods)
        val lpCount = nonFracturedMods.countOfMatches(args.lowPriorityMods)
        return makeAndFuseDecision(item = item, hpCount = hpCount, lpCount = lpCount)
    }

    /**
     * Make a decision based on item. Also predict the next decision and
     * possibly fuse both (e.g. [2 mod annul, 1 mod exalt] fuse into chaos)
     */
    private fun makeAndFuseDecision(
        item: PoeRollableItem,
        hpCount: Int,
        lpCount: Int,
    ): CraftDecisionMakerV2.Decision {
        val fracCount = item.explicitMods.count { it.fractured }
        // Multi-frac item is not possible (yet) in POE2
        require(fracCount <= 1)

        // Including the optional fractured mod
        val goodModCount = hpCount + lpCount + fracCount
        val badModCount = item.explicitMods.size - goodModCount

        return when {
            hpCount > 0 && goodModCount >= args.desiredModCount -> {
                CraftDecisionMakerV2.Decision(null, "Good mods $goodModCount >= desired ${args.desiredModCount}")
            }

            hpCount > 0 && badModCount == 0 -> {
                CraftDecisionMakerV2.Decision(
                    args.exaltType,
                    "High priority mods $hpCount, but total mods $goodModCount not enough"
                )
            }

            badModCount == 0 || badModCount == 1 && hpCount > 0 -> {
                // Either all low-priority mods, or high-priority + one bad mod
                val why = if (badModCount == 0) {
                    "all low-priority mod"
                } else {
                    "mix of high-priority + bad mod, fish for chaos"
                }
                CraftDecisionMakerV2.Decision(PoeCurrency.Companion.Chaos, why)
            }

            item.explicitMods.size == 1 + fracCount -> {
                require(badModCount == 1)
                CraftDecisionMakerV2.Decision(PoeCurrency.Companion.Chaos, "1 bad mod")
            }

            else -> {
                require(badModCount > 0)
                CraftDecisionMakerV2.Decision(PoeCurrency.Companion.Annul, "$badModCount bad mod")
            }
        }
    }

    class Args(
        /**
         * The best mods, often with low mod weight (i.e. harder to roll).
         * For efficiency's purpose, they are initially rolled with chaos instead of exalt+annul,
         * because perfect exalt + annul are more scarce than chaos.
         */
        val highPriorityMods: List<PoeRollableItem.ExplicitMod.Matcher>,
        /**
         * Also consider good mods, but lower priority than [highPriorityMods].
         * These should have higher mod weight (easier to roll), so using perfect exalt + annul for them are fine.
         */
        val lowPriorityMods: List<PoeRollableItem.ExplicitMod.Matcher>,
        /**
         * Number of mods in an item that's considered "done". This includes the optional fractured mod.
         */
        val desiredModCount: Int,
        /**
         * The exalt type to be used to add a mod.
         */
        val exaltType: PoeCurrency.TieredType = PoeCurrency.Companion.Exalt.asPerfect(),
    ) {
        init {
            require(desiredModCount >= 1)
            require(highPriorityMods.isNotEmpty())
            require(exaltType.kind == PoeCurrency.CanHaveTier.Exalt)
            // We don't know if the incoming item is fractured, so +1 to be conservative.
            require(highPriorityMods.size + lowPriorityMods.size + 1 >= desiredModCount)
        }
    }
}