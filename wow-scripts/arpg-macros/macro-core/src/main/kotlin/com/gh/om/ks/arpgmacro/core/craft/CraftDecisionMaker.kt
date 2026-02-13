package com.gh.om.ks.arpgmacro.core.craft

import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem

/**
 * Decides the next crafting action based on an item's current mods.
 */
fun interface CraftDecisionMaker {
    fun getDecision(item: PoeRollableItem): Decision

    data class Decision(
        val type: DecisionType,
        val why: String,
    ) : com.gh.om.ks.arpgmacro.core.CheckResult {
        val done: Boolean
            get() = type == DecisionType.Done

        override val isGood: Boolean
            get() = done
    }

    enum class DecisionType {
        Done,
        Reset,
        Proceed,
        GoBack,
    }

    /**
     * Matches mods by a predicate, checking all explicit mods regardless of side.
     */
    class ByDesiredModsEx(
        private val desiredModCount: Int,
        private val doesModMatch: (PoeRollableItem.ExplicitMod) -> Boolean,
    ) : CraftDecisionMaker {
        override fun getDecision(item: PoeRollableItem): Decision {
            val matches = item.explicitMods.count(doesModMatch)
            return byMatches(
                matches = matches,
                desiredModCount = desiredModCount,
                nMods = item.explicitMods.size,
            )
        }
    }

    /**
     * Matches mods on one side (prefix or suffix) only. For alt-aug-regal crafting
     * where regal can land on either side, forcing a reset if the regal misses.
     */
    class ByDesiredOneSideModsEx(
        private val side: PoeRollableItem.ExplicitModLocation,
        private val desiredModCount: Int,
        private val getMatchedMods: (List<PoeRollableItem.ExplicitMod>) -> Int,
    ) : CraftDecisionMaker {
        override fun getDecision(item: PoeRollableItem): Decision {
            val modsOnSide = item.explicitMods.filter { it.loc == side }
            val matches = getMatchedMods(modsOnSide)
            if (item.rarity == PoeRollableItem.Rarity.Rare &&
                matches < desiredModCount
            ) {
                return Decision(
                    type = DecisionType.Reset,
                    why = "Only $matches matches after regal",
                )
            }
            return byMatches(
                matches = matches,
                desiredModCount = desiredModCount,
                nMods = modsOnSide.size,
            )
        }
    }

    companion object {
        /**
         * @param matches The number of matched affixes on the current item
         * @param desiredModCount The number of desired affixes on a fully crafted item
         * @param nMods The number of mods on the current item
         */
        fun byMatches(
            matches: Int,
            desiredModCount: Int,
            nMods: Int,
        ): Decision {
            val type: DecisionType
            val why: String
            when {
                matches >= desiredModCount -> {
                    type = DecisionType.Done
                    why = "Matches $matches mods is more than desired $desiredModCount"
                }

                matches == nMods -> {
                    type = DecisionType.Proceed
                    why = "All $nMods mods match"
                }

                matches == nMods - 1 && nMods == 4 -> {
                    type = DecisionType.GoBack
                    why = "All $nMods but 1 mod match"
                }

                else -> {
                    type = DecisionType.Reset
                    why = "Only $matches matches within $nMods"
                }
            }
            return Decision(type, why)
        }

        fun byDesiredMods(
            desiredModNames: List<String>,
            desiredModCount: Int,
        ): CraftDecisionMaker = ByDesiredModsEx(
            desiredModCount = desiredModCount,
        ) {
            it.name in desiredModNames
        }

        fun byDesiredOneSideMods(
            desiredModNames: List<String>,
            side: PoeRollableItem.ExplicitModLocation,
            desiredModCount: Int = desiredModNames.size,
            nameGetter: (PoeRollableItem.ExplicitMod) -> String = { it.name },
            extraCheck: (PoeRollableItem.ExplicitMod) -> Boolean = { true },
        ): CraftDecisionMaker {
            return ByDesiredOneSideModsEx(side = side, desiredModCount = desiredModCount) { mods ->
                mods.count {
                    nameGetter(it) in desiredModNames && extraCheck(it)
                }
            }
        }

        fun matchesDescription(mod: PoeRollableItem.ExplicitMod, descriptions: List<String>): Boolean {
            return descriptions.any { it in mod.description }
        }
    }

}

/**
 * Adapts a [CraftDecisionMaker] to an [com.gh.om.ks.arpgmacro.core.ItemChecker] for use with [com.gh.om.ks.arpgmacro.core.MultiRollLoop].
 */
fun CraftDecisionMaker.asItemChecker(): com.gh.om.ks.arpgmacro.core.ItemChecker<CraftDecisionMaker.Decision> {
    return object : com.gh.om.ks.arpgmacro.core.ItemChecker<CraftDecisionMaker.Decision> {
        override fun evaluate(item: PoeRollableItem): CraftDecisionMaker.Decision {
            return getDecision(item)
        }

        override fun generateReport(results: List<CraftDecisionMaker.Decision>): String {
            return "Ok"
        }
    }
}

fun CraftDecisionMakerV2.asItemChecker(): com.gh.om.ks.arpgmacro.core.ItemChecker<CraftDecisionMakerV2.Decision> {
    return object : com.gh.om.ks.arpgmacro.core.ItemChecker<CraftDecisionMakerV2.Decision> {
        override fun evaluate(item: PoeRollableItem): CraftDecisionMakerV2.Decision {
            return getDecision(item)
        }

        override fun generateReport(results: List<CraftDecisionMakerV2.Decision>): String {
            return "Ok"
        }
    }
}

