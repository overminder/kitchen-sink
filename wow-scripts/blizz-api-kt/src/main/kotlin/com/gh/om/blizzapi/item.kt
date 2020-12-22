package com.gh.om.blizzapi

import com.google.gson.annotations.SerializedName

data class Item(
    val id: String,
    val name: String,
    // i.e. ilevel
    val level: Int,
    @SerializedName("preview_item")
    val previewItem: Preview,
    @SerializedName("item_class")
    val klass: Klass.Named,
    @SerializedName("item_subclass")
    val subclass: Subclass.Named,
    @SerializedName("inventory_type")
    val inventory: Inventory.Named,
    val quality: Quality.Named,
) {

    fun findStat(stat: Item.Stat): Item.Stat.Valued? {
        return previewItem.stats.find { it.type.type == stat }
    }

    data class Preview(
        val stats: List<Stat.Valued>,
    )

    // All these enums are copied from simc's source code.
    enum class Klass {
        CONSUMABLE,
        CONTAINER,
        WEAPON,
        GEM,
        ARMOR,
        REAGENT,
        PROJECTILE,
        TRADE_GOODS,
        GENERIC,
        RECIPE,
        MONEY,
        QUIVER,
        QUEST,
        KEY,
        PERMANENT,
        MISC,
        GLYPH;

        data class Named(
            val name: String,
            val id: Klass
        )
    }

    enum class Subclass {
        AXE,
        AXE2,
        BOW,
        GUN,
        MACE,
        MACE2,
        POLEARM,
        SWORD,
        SWORD2,
        WARGLAIVE,
        STAFF,
        EXOTIC,
        EXOTIC2,
        FIST,
        MISC,
        DAGGER,
        THROWN,
        SPEAR,
        CROSSBOW,
        WAND,
        FISHING_POLE,
        INVALID;

        data class Named(
            val name: String,
            val id: Subclass
        )
    }

    enum class Stat {
        STAMINA,

        // Primary stats
        AGILITY,
        INTELLECT,
        STRENGTH,

        // Secondary stats
        CRIT_RATING,
        HASTE_RATING,
        MASTERY_RATING,
        VERSATILITY;

        companion object {
            val secondaryStats = listOf(
                CRIT_RATING,
                HASTE_RATING,
                MASTERY_RATING,
                VERSATILITY
            )
            val primaryStats = listOf(
                STRENGTH,
                AGILITY,
                INTELLECT
            )
        }

        fun isCombatRating(): Boolean {
            return secondaryStats.contains(this)
        }

        data class Valued(
            val type: Named,
            val value: Int,
        )

        data class Named(
            val type: Stat?,
            val name: String
        )
    }

    enum class Inventory {
        NON_EQUIP,
        HEAD,
        NECK,
        SHOULDERS,
        BODY,
        CHEST,
        WAIST,
        LEGS,
        FEET,
        WRISTS,
        HANDS,
        FINGER,
        TRINKET,
        WEAPON,
        SHIELD,
        RANGED,
        CLOAK,
        TWOHWEAPON,
        BAG,
        TABARD,
        ROBE,
        WEAPONMAINHAND,
        WEAPONOFFHAND,
        HOLDABLE,
        AMMO,
        THROWN,
        RANGEDRIGHT,
        QUIVER,
        RELIC,
        MAX;

        data class Named(
            val type: Inventory,
            val name: String
        )
    }

    enum class Quality {
        POOR,
        COMMON,
        UNCOMMON,
        RARE,
        EPIC,
        LEGENDARY,
        ARTIFACT;

        data class Named(
            val type: Quality,
            val name: String
        )

        fun isAtLeast(other: Quality) = ordinal >= other.ordinal
    }
}
