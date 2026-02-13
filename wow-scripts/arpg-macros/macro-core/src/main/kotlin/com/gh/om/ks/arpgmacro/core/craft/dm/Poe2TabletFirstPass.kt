package com.gh.om.ks.arpgmacro.core.craft.dm

import com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMakerV2
import com.gh.om.ks.arpgmacro.core.craft.countOfMatches
import com.gh.om.ks.arpgmacro.core.item.PoeCurrency
import com.gh.om.ks.arpgmacro.core.item.PoeItem
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem
import com.gh.om.ks.arpgmacro.core.item.affixThat
import com.gh.om.ks.arpgmacro.core.item.isPrefix
import com.gh.om.ks.arpgmacro.core.item.isSuffix

/** Tablets can have at most 2 prefixes and 2 suffixes. */
private const val MAX_PREFIX_SUFFIX = 2

/**
 * The "first pass" of POE2 precursor tablet rolling is to cheaply fish for mods on lots of tablets.
 * The rolling will stop if the tablet item has [Args.desiredGoodModCount] good mods (matched by [Args.goodMods]),
 * or when the item is "bricked" to save currency.
 * The flow is (stop when item has enough good mods):
 * - Transmute on normal item: becomes 1-mod magic item.
 * - Aug on magic 1 mod-item: becomes 2-mod magic item.
 * - If any mod is good, regal to become 3-mod rare item. Otherwise, the item is "bricked".
 * - If it's possible for exalt to add another good mod, exalt. Otherwise, the item is "bricked"
 */
class Poe2TabletFirstPass(
    val args: Args,
) : CraftDecisionMakerV2 {
    override fun getDecision(item: PoeRollableItem): CraftDecisionMakerV2.Decision {
        val mods = item.explicitMods
        val goodCount = mods.countOfMatches(args.goodMods)

        return when {
            goodCount >= args.desiredGoodModCount ->
                // Done check at every step
                CraftDecisionMakerV2.Decision(null, "Has $goodCount good mod(s), done")

            item.rarity == PoeRollableItem.Rarity.Normal -> {
                CraftDecisionMakerV2.Decision(args.trans, "Normal, transmuting")
            }

            item.rarity == PoeRollableItem.Rarity.Magic && mods.size <= 1 -> {
                CraftDecisionMakerV2.Decision(args.aug, "Magic ${mods.size} mod(s), augmenting")
            }

            item.rarity == PoeRollableItem.Rarity.Magic -> {
                // 2+ mod magic: regal if any good mod, else bricked
                if (goodCount > 0) {
                    CraftDecisionMakerV2.Decision(args.regal, "Magic ${mods.size} mods, $goodCount good, regaling")
                } else {
                    CraftDecisionMakerV2.Decision(null, "Magic ${mods.size} mods, 0 good, bricked")
                }
            }

            item.rarity == PoeRollableItem.Rarity.Rare && mods.size <= 3 -> {
                // Just regaled: exalt if possible, else bricked
                if (canExaltHitGoodMod(item)) {
                    CraftDecisionMakerV2.Decision(args.exalt, "Rare ${mods.size} mods, exalting")
                } else {
                    CraftDecisionMakerV2.Decision(null, "Rare ${mods.size} mods, can't hit good, bricked")
                }
            }

            item.rarity == PoeRollableItem.Rarity.Rare -> {
                // 4+ mod rare: past first-pass budget, bricked
                CraftDecisionMakerV2.Decision(null, "Rare ${mods.size} mods, $goodCount good, bricked")
            }

            else -> error("Unexpected rarity: ${item.rarity}")
        }
    }

    fun score(item: PoeItem): Double {
        val ritem = item as? PoeRollableItem ?: return 0.0
        val goodCount = ritem.explicitMods.countOfMatches(args.goodMods)
        return goodCount.toDouble()
    }

    private fun canExaltHitGoodMod(item: PoeRollableItem): Boolean {
        val prefixCount = item.affixThat { it.isPrefix }.count()
        val suffixCount = item.affixThat { it.isSuffix }.count()
        return args.goodMods.any { matcher ->
            when (matcher.loc) {
                PoeRollableItem.ExplicitModLocation.Prefix -> prefixCount < MAX_PREFIX_SUFFIX
                PoeRollableItem.ExplicitModLocation.Suffix -> suffixCount < MAX_PREFIX_SUFFIX
                null -> error("All good mod matchers must have loc")
            }
        }
    }

    class Args(
        val goodMods: List<PoeRollableItem.ExplicitMod.Matcher>,
        /**
         * How many [goodMods] mods are needed.
         */
        val desiredGoodModCount: Int = 2,
        val trans: PoeCurrency.TieredType = PoeCurrency.Trans.asGreater(),
        val aug: PoeCurrency.TieredType = PoeCurrency.Aug.asGreater(),
        val regal: PoeCurrency.TieredType = PoeCurrency.Regal.asGreater(),
        val exalt: PoeCurrency.TieredType = PoeCurrency.Exalt.asGreater(),
    ) {
        init {
            require(goodMods.all { it.loc != null })
        }
    }
}
