package com.gh.om.blizzapi

import com.gh.om.blizzapi.base.Simc
import javax.inject.Inject

class ItemScalingImpl @Inject constructor(
    private val simc: Simc.DB
) : Simc.ItemScaling {
    override fun normStat(item: Item, stat: Item.Stat, statVal: Int): Double {
        val crType = requireNotNull(combatRatingType(item.inventory.type))
        val budget = itemStatBudget(item, item.level)
        val crCoeff = coeffForStat(stat, item.level, crType)
        return statVal / crCoeff * 10000.0 / budget
    }

    override fun scaledStat(item: Item, toIlevel: Int, statAlloc: Double, stat: Item.Stat): Int {
        require(item.quality.type.isAtLeast(Item.Quality.UNCOMMON))
        val budget = itemStatBudget(item, toIlevel)

        // Simc was rounding to the nearest tenth, but that doesn't seem to be 100% accurate...
        val raw = statAlloc * budget * 0.0001 + 0.1
        val crType = requireNotNull(combatRatingType(item.inventory.type))
        val crCoeff = coeffForStat(stat, toIlevel, crType)
        return (raw * crCoeff).toInt()
    }

    private fun getBudgetType(item: Item): Simc.BudgetType? = when (item.klass.id) {
        Item.Klass.WEAPON -> when (item.subclass.id) {
            Item.Subclass.AXE2,
            Item.Subclass.MACE2,
            Item.Subclass.POLEARM,
            Item.Subclass.SWORD2,
            Item.Subclass.STAFF,
            Item.Subclass.GUN,
            Item.Subclass.BOW,
            Item.Subclass.CROSSBOW,
            Item.Subclass.THROWN -> Simc.BudgetType.LARGE
            else -> Simc.BudgetType.TINY
        }
        Item.Klass.ARMOR -> when (item.inventory.type) {
            Item.Inventory.HEAD,
            Item.Inventory.CHEST,
            Item.Inventory.LEGS,
            Item.Inventory.ROBE -> Simc.BudgetType.LARGE
            Item.Inventory.SHOULDER,
            Item.Inventory.WAIST,
            Item.Inventory.FEET,
            Item.Inventory.HAND,
            Item.Inventory.TRINKET -> Simc.BudgetType.MEDIUM
            Item.Inventory.NECK,
            Item.Inventory.FINGER,
            Item.Inventory.CLOAK,
            Item.Inventory.WRIST -> Simc.BudgetType.SMALL
            Item.Inventory.WEAPONOFFHAND,
            Item.Inventory.HOLDABLE,
            Item.Inventory.SHIELD -> Simc.BudgetType.TINY
            else -> null
        }
        else -> null
    }

    private fun itemStatBudget(item: Item, level: Int): Double {
        val budgetType = requireNotNull(getBudgetType(item))
        val ilevelData = requireNotNull(simc.randPropPointsByIlevel[level])

        val budgetTable = when (item.quality.type) {
            Item.Quality.EPIC, Item.Quality.LEGENDARY -> ilevelData.epic
            Item.Quality.RARE, Item.Quality.ARTIFACT -> ilevelData.rare
            else -> ilevelData.uncommon
        }
        return budgetTable[budgetType.ordinal].also { require(it > 0) }
    }

    private fun coeffForStat(stat: Item.Stat, level: Int, crType: Simc.CrmType): Double {
        return when {
            stat.isCombatRating() -> combatRatingMultiplier(level, crType)
            stat == Item.Stat.STAMINA -> stamMultiplier(level, crType)
            else -> 1.0
        }
    }

    private fun combatRatingMultiplier(level: Int, crType: Simc.CrmType): Double {
        return requireNotNull(simc.crmTable[crType]?.get(level - 1))
    }

    private fun stamMultiplier(level: Int, crType: Simc.CrmType): Double {
        return requireNotNull(simc.stamCrmTable[crType]?.get(level - 1))
    }

    private fun combatRatingType(type: Item.Inventory): Simc.CrmType? {
        return when (type) {
            Item.Inventory.NECK,
            Item.Inventory.FINGER -> Simc.CrmType.JEWLERY
            Item.Inventory.TRINKET -> Simc.CrmType.TRINKET

            Item.Inventory.WEAPON,
            Item.Inventory.TWOHWEAPON,
            Item.Inventory.WEAPONMAINHAND,
            Item.Inventory.WEAPONOFFHAND,
            Item.Inventory.RANGED,
            Item.Inventory.RANGEDRIGHT,
            Item.Inventory.THROWN -> Simc.CrmType.WEAPON

            Item.Inventory.ROBE,
            Item.Inventory.HEAD,
            Item.Inventory.SHOULDER,
            Item.Inventory.CHEST,
            Item.Inventory.CLOAK,
            Item.Inventory.BODY,
            Item.Inventory.WRIST,
            Item.Inventory.WAIST,
            Item.Inventory.LEGS,
            Item.Inventory.FEET,
            Item.Inventory.SHIELD,
            Item.Inventory.HOLDABLE,
            Item.Inventory.HAND -> Simc.CrmType.ARMOR

            else -> null
        }
    }
}