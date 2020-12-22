package com.gh.om.blizzapi

import javax.inject.Inject

class ItemScaling @Inject constructor(
    private val simc: Simc
) {
    enum class BudgetType {
        LARGE,
        MEDIUM,
        SMALL,
        TINY,
    }

    // Combat rating multiplier type
    enum class CrmType {
        ARMOR,
        WEAPON,
        TRINKET,
        JEWLERY;
    }

    fun getBudgetType(item: Item): BudgetType? = when (item.klass.id) {
        Item.Klass.WEAPON -> when (item.subclass.id) {
            Item.Subclass.AXE2,
            Item.Subclass.MACE2,
            Item.Subclass.POLEARM,
            Item.Subclass.SWORD2,
            Item.Subclass.STAFF,
            Item.Subclass.GUN,
            Item.Subclass.BOW,
            Item.Subclass.CROSSBOW,
            Item.Subclass.THROWN -> BudgetType.LARGE
            else -> BudgetType.TINY
        }
        Item.Klass.ARMOR -> when (item.inventory.type) {
            Item.Inventory.HEAD,
            Item.Inventory.CHEST,
            Item.Inventory.LEGS,
            Item.Inventory.ROBE -> BudgetType.LARGE
            Item.Inventory.SHOULDERS,
            Item.Inventory.WAIST,
            Item.Inventory.FEET,
            Item.Inventory.HANDS,
            Item.Inventory.TRINKET -> BudgetType.MEDIUM
            Item.Inventory.NECK,
            Item.Inventory.FINGER,
            Item.Inventory.CLOAK,
            Item.Inventory.WRISTS -> BudgetType.SMALL
            Item.Inventory.WEAPONOFFHAND,
            Item.Inventory.HOLDABLE,
            Item.Inventory.SHIELD -> BudgetType.TINY
            else -> null
        }
        else -> null
    }

    fun normStat(item: Item): Double {
        val crType = combatRatingType(item.inventory.type) ?: return 1.0
        val crCoeff = combatRatingMultiplier(item.level, crType)
        val budget = itemStatBudget(item, item.level)
        return 10000.0 / (crCoeff * budget)
    }

    fun scaledStat(item: Item, toIlevel: Int, statAlloc: Int, stat: Item.Stat): Int {
        require(item.quality.type.isAtLeast(Item.Quality.UNCOMMON))
        val budget = itemStatBudget(item, toIlevel)

        // Round to the nearest tenth
        val raw = (statAlloc * budget * 0.0001 + 0.5).toInt()
        if (stat.isCombatRating()) {
            val crType = combatRatingType(item.inventory.type) ?: return raw
            val crCoeff = combatRatingMultiplier(item.level, crType)
            return (raw * crCoeff).toInt()
        } else if (stat == Item.Stat.STAMINA) {
        }

        return raw
    }

    private fun itemStatBudget(item: Item, ilevel: Int): Double {
        val budgetType = requireNotNull(getBudgetType(item))
        val ilevelData = requireNotNull(simc.randPropPoints.find { it.ilevel == ilevel })

        val budgetTable = when (item.quality.type) {
            Item.Quality.EPIC, Item.Quality.LEGENDARY -> ilevelData.epic
            Item.Quality.RARE, Item.Quality.ARTIFACT -> ilevelData.rare
            else -> ilevelData.uncommon
        }
        return budgetTable[budgetType.ordinal].also { require(it > 0) }
    }

    private fun combatRatingMultiplier(level: Int, crType: CrmType): Double {
        return requireNotNull(simc.crmTable[crType]?.get(level))
    }

    private fun combatRatingType(type: Item.Inventory): CrmType? {
        return when (type) {
            Item.Inventory.NECK,
            Item.Inventory.FINGER -> CrmType.JEWLERY
            Item.Inventory.TRINKET -> CrmType.TRINKET

            Item.Inventory.WEAPON,
            Item.Inventory.TWOHWEAPON,
            Item.Inventory.WEAPONMAINHAND,
            Item.Inventory.WEAPONOFFHAND,
            Item.Inventory.RANGED,
            Item.Inventory.RANGEDRIGHT,
            Item.Inventory.THROWN -> CrmType.WEAPON


            Item.Inventory.ROBE,
            Item.Inventory.HEAD,
            Item.Inventory.SHOULDERS,
            Item.Inventory.CHEST,
            Item.Inventory.CLOAK,
            Item.Inventory.BODY,
            Item.Inventory.WRISTS,
            Item.Inventory.WAIST,
            Item.Inventory.LEGS,
            Item.Inventory.FEET,
            Item.Inventory.SHIELD,
            Item.Inventory.HOLDABLE,
            Item.Inventory.HANDS -> CrmType.ARMOR

            else -> null
        }
    }
}