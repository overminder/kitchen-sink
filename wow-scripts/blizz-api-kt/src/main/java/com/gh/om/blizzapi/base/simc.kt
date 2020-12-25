package com.gh.om.blizzapi.base

import com.gh.om.blizzapi.Item

// Mostly copied from simc's source.
object Simc {
    // Modeled from simc's random_prop_data_t.
    data class RandomProp(
        val ilevel: Int,
        val epic: List<Double>,
        val rare: List<Double>,
        val uncommon: List<Double>,
    )

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

    sealed class SlotCombination {
        data class Just(val slot: Slot) : SlotCombination()
        data class And(val slots: List<Slot>) : SlotCombination()
        data class Or(val slots: List<Slot>) : SlotCombination()
    }

    enum class Slot {
        HEAD,
        NECK,
        SHOULDER,
        CHEST,
        WAIST,
        LEGS,
        FEET,
        WRIST,
        HANDS,
        FINGER1,
        FINGER2,
        TRINKET1,
        TRINKET2,
        BACK,
        MAIN_HAND,
        OFF_HAND;
    }

    object Lang {
        data class Item(
            val slot: Slot,
            val id: Int,
            val bonusIds: List<Int> = emptyList(),
            val gemIds: List<Int> = emptyList(),
            val is2hWeapon: Boolean = false,
        )

        interface Reader {
            suspend fun readItems(source: String): List<Item>
        }

        enum class WeaponKind {
            MAIN_HAND,
            OFF_HAND,
            TWO_HAND,
        }
    }

    interface EquipmentStateFactory {
        fun create(): EquipmentState
    }

    interface EquipmentState {
        val items: Collection<Lang.Item>

        fun equip(item: Lang.Item)
        fun copy(): EquipmentState

        fun diff(other: EquipmentState): List<Pair<Lang.Item?, Lang.Item?>>
    }

    interface DB {
        val randPropPointsByIlevel: Map<Int, RandomProp>
        val crmTable: Map<CrmType, List<Double>>
        val stamCrmTable: Map<CrmType, List<Double>>

        fun inventoryToSlot(inventory: Item.Inventory): SlotCombination?

        fun tryTradeGearToken(itemId: Int): List<Int>?
    }

    interface CxxSourceReader {
        fun getRandPropPoints(): List<RandomProp>
        fun getCrmTable(): Map<CrmType, List<Double>>
        fun getStamCrmTable(): Map<CrmType, List<Double>>
    }

    interface ItemScaling {
        fun normStat(item: Item, stat: Item.Stat, statVal: Int): Double
        fun scaledStat(item: Item, toIlevel: Int, statAlloc: Double, stat: Item.Stat): Int
    }
}