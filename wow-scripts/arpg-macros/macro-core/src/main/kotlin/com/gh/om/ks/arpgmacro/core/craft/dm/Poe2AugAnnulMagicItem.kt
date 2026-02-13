package com.gh.om.ks.arpgmacro.core.craft.dm

import com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMakerV2
import com.gh.om.ks.arpgmacro.core.craft.countOfMatches
import com.gh.om.ks.arpgmacro.core.item.PoeCurrency
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem

/**
 * Crafts on a normal or magic item (which has at most 2 mods: 1 prefix + 1 suffix), via perfect aug + annul combo.
 * The end goal is to have at least [Args.desiredHpModCount] high-priority (HP) mods.
 */
class Poe2AugAnnulMagicItem(
    val args: Args,
) : CraftDecisionMakerV2 {
    override fun getDecision(item: PoeRollableItem): CraftDecisionMakerV2.Decision {
        require(item.rarity.isAtMost(PoeRollableItem.Rarity.Magic)) {
            "Must be <= magic, but got ${item.rarity}"
        }

        val mods = item.explicitMods
        val hpCount = mods.countOfMatches(args.highPriorityMods)

        return when (mods.size) {
            0 -> {
                // Add a mod: transmute on normal, aug on magic
                val currency = if (item.rarity == PoeRollableItem.Rarity.Normal) {
                    PoeCurrency.Companion.Trans.asPerfect()
                } else {
                    PoeCurrency.Companion.Aug.asPerfect()
                }
                CraftDecisionMakerV2.Decision(currency, "0 mods, adding one")
            }

            1 -> {
                if (hpCount >= args.desiredHpModCount) {
                    CraftDecisionMakerV2.Decision(null, "Has $hpCount HP mod(s), done")
                } else {
                    // Check if aug can still hit an HP mod based on mod locations
                    val existingLoc = mods.single().loc
                    val canAugHitHp = args.highPriorityMods.any { it.loc != existingLoc }
                    if (canAugHitHp) {
                        CraftDecisionMakerV2.Decision(
                            PoeCurrency.Companion.Aug.asPerfect(),
                            "1 non-HP mod, aug can hit HP"
                        )
                    } else {
                        CraftDecisionMakerV2.Decision(PoeCurrency.Companion.Annul, "1 non-HP mod, aug can't hit HP")
                    }
                }
            }

            2 -> {
                if (hpCount >= args.desiredHpModCount) {
                    CraftDecisionMakerV2.Decision(null, "Has $hpCount HP mod(s), done")
                } else {
                    CraftDecisionMakerV2.Decision(PoeCurrency.Companion.Annul, "2 mods, $hpCount HP mod(s), annulling")
                }
            }

            else -> error("Magic item should have at most 2 mods, got ${mods.size}")
        }
    }

    class Args(
        /**
         * The result must have this mod.
         */
        val highPriorityMods: List<PoeRollableItem.ExplicitMod.Matcher>,
        /**
         * How many [highPriorityMods] mods are needed. At most 2 for magic items.
         */
        val desiredHpModCount: Int = 1,
    ) {
        init {
            require(highPriorityMods.isNotEmpty())
            require(highPriorityMods.size >= desiredHpModCount)
            require(desiredHpModCount in 1..2)
            if (desiredHpModCount == 2) {
                // Most have looking for prefix and suffix.
                require(highPriorityMods.map { it.loc }.toSet().size == 2)
            }
            require(highPriorityMods.all { it.loc != null }) {
                "Efficient crafting on magic items requires knowing all desired mod location. But got $highPriorityMods"
            }
        }
    }
}