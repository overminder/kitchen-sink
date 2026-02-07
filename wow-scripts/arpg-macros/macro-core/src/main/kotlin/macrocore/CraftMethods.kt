package macrocore

/**
 * Interface for applying currency to an item. Shared between real game
 * interaction and test simulators.
 */
interface PoeItemCrafter {
    suspend fun getCurrentItem(): PoeRollableItem

    suspend fun transmute()
    suspend fun alternate()
    suspend fun augment()
    suspend fun regal()
    suspend fun exalt()
    suspend fun scour()
    suspend fun annul()
    suspend fun chaos()
    suspend fun alch()
    suspend fun armourerScrap()
    suspend fun whetstone()
}

/**
 * Crafting state machine. Each call advances one step based on item rarity
 * and the decision maker's output.
 */
object CraftMethods {
    suspend fun scourAlchOnce(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
    ): CraftDecisionMaker.Decision {
        val item = c.getCurrentItem()
        val decision = dm.getDecision(item)
        if (decision.type == CraftDecisionMaker.DecisionType.Done) {
            return decision
        }

        val why: String
        when (item.rarity) {
            PoeRollableItem.Rarity.Normal -> {
                why = "alch because normal"
                c.alch()
            }
            PoeRollableItem.Rarity.Magic -> {
                why = "scour - alch because magic"
                c.scour()
                c.alch()
            }
            PoeRollableItem.Rarity.Rare -> {
                why = "chaos because rare"
                c.scour()
                c.alch()
            }
            PoeRollableItem.Rarity.Unique -> {
                error("Can't roll unique")
            }
        }
        return decision.copy(why = decision.why + ", impl = " + why)
    }

    suspend fun chaosOnce(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
    ): CraftDecisionMaker.Decision {
        val item = c.getCurrentItem()
        val decision = dm.getDecision(item)
        if (decision.type == CraftDecisionMaker.DecisionType.Done) {
            return decision
        }

        val why: String
        when (item.rarity) {
            PoeRollableItem.Rarity.Normal -> {
                why = "alch because normal"
                c.alch()
            }
            PoeRollableItem.Rarity.Magic -> {
                why = "scour - alch because magic"
                c.scour()
                c.alch()
            }
            PoeRollableItem.Rarity.Rare -> {
                why = "chaos because rare"
                c.chaos()
            }
            PoeRollableItem.Rarity.Unique -> {
                error("Can't roll unique")
            }
        }
        return decision.copy(why = decision.why + ", impl = " + why)
    }

    /**
     * Alt-only mode. Useful for 1 prefix + 1 suffix recomb where we want
     * to avoid augmenting the other side.
     */
    suspend fun altOnce(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
    ): CraftDecisionMaker.Decision = altAugRegalExaltOnceEx(c = c, dm = dm, altOnly = true)

    suspend fun altAugRegalExaltOnce(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
    ): CraftDecisionMaker.Decision = altAugRegalExaltOnceEx(c = c, dm = dm, altOnly = false)

    private suspend fun altAugRegalExaltOnceEx(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
        altOnly: Boolean,
    ): CraftDecisionMaker.Decision {
        val item = c.getCurrentItem()
        val decision = dm.getDecision(item)
        if (decision.type == CraftDecisionMaker.DecisionType.Done) {
            return decision
        }

        val shouldProceed = decision.type == CraftDecisionMaker.DecisionType.Proceed
        val shouldGoBack = decision.type == CraftDecisionMaker.DecisionType.GoBack

        if (altOnly && shouldProceed) {
            require(item.explicitMods.isEmpty()) {
                "altOnly should only target 1 mod items (i.e. should not proceed on item with ${item.explicitMods.size} mods)"
            }
        }

        val why: String
        val isHeistSpecialBase = "Simplex Amulet" in item.originalDescription

        when (item.rarity) {
            PoeRollableItem.Rarity.Normal -> {
                require(!shouldGoBack)
                if (isHeistSpecialBase) {
                    why = "alch because heist special base"
                    c.alch()
                } else {
                    why = "transmute because normal"
                    c.transmute()
                }
            }
            PoeRollableItem.Rarity.Magic -> {
                require(!shouldGoBack)
                if (isHeistSpecialBase) {
                    c.regal()
                    why = "regal because magic heist special base can't have any mods"
                } else {
                    when (val nmods = item.explicitMods.size) {
                        0 -> {
                            why = "aug because 0 mod magic item"
                            c.augment()
                        }
                        1 -> {
                            if (shouldProceed) {
                                why = "aug 1 mod to 2 mods"
                                c.augment()
                            } else {
                                why = "alt to reset"
                                c.alternate()
                            }
                        }
                        2 -> {
                            if (shouldProceed) {
                                why = "regal magic to rare"
                                c.regal()
                            } else {
                                why = "alt to reset magic item"
                                c.alternate()
                            }
                        }
                        else -> {
                            error("Shouldn't happen: magic item has $nmods mods")
                        }
                    }
                }
            }
            PoeRollableItem.Rarity.Rare -> {
                if (shouldProceed) {
                    c.exalt()
                    why = "exalt to add mod"
                } else if (shouldGoBack) {
                    c.annul()
                    why = "annul to go back"
                } else {
                    c.scour()
                    why = "scour to reset"
                }
            }
            PoeRollableItem.Rarity.Unique -> {
                error("Can't roll unique")
            }
        }
        return decision.copy(why = decision.why + ", impl = " + why)
    }
}
