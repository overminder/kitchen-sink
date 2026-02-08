package com.gh.om.ks.arpgmacro.core

sealed interface PoeItem {
    sealed interface Klass {
        companion object {
            fun fromRepr(repr: String): Klass? {
                return ConstKlass.entries.firstOrNull { it.repr == repr }
            }
        }
    }

    enum class ConstKlass(val repr: String) : Klass {
        Currency("Stackable Currency"),
        Map("Maps"),
        MiscMap("Misc Map Items"),
        Jewels("Jewels"),
    }

    enum class MapTier {
        Other,
        T16_5,
        T17,
    }

    data class Map(val tier: MapTier) : Klass

    data class Weapon(val kind: String) : Klass
    data class Armor(val kind: ArmorKind) : Klass

    enum class ArmorKind(val repr: String) {
        Body("Body Armours"),
        Helm("Helmets"),
        Shield("Shields"),
        Gloves("Gloves"),
        Boots("Boots"),
        Belt("Belts"),
        Ring("Rings"),
        Amulet("Amulets");

        companion object {
            fun fromRepr(repr: String): ArmorKind? {
                return entries.firstOrNull { it.repr == repr }
            }
        }
    }
}

fun PoeItem.Klass?.isMapLike(): Boolean {
    return when (this) {
        PoeItem.ConstKlass.Map,
        PoeItem.ConstKlass.MiscMap,
        is PoeItem.Map -> true
        else -> false
    }
}

data class PoeCurrency(
    val type: Type,
    val stackSize: Int,
) : PoeItem {
    interface Type

    enum class KnownType(val repr: String) : Type {
        Chaos("Chaos Orb"),
        Scour("Orb of Scouring"),
        Alch("Orb of Alchemy"),
        Binding("Orb of Binding"),
    }

    object UnknownType : Type
}

data class PoeRollableItem(
    val klass: PoeItem.Klass?,
    val rarity: Rarity,
    val explicitMods: List<ExplicitMod>,
    val qualities: List<Quality>,
    val originalDescription: String,
) : PoeItem {

    enum class Rarity {
        Normal,
        Magic,
        Rare,
        Unique,
    }

    enum class ExplicitModLocation {
        Prefix,
        Suffix,
    }

    data class ExplicitMod(
        val loc: ExplicitModLocation,
        val name: String,
        val tier: Int?,
        val description: String,
    )

    data class Quality(
        val name: QualName,
        val value: Int,
    )

    sealed class QualName {
        data class FromCurrency(val ty: AugType) : QualName()
        data class Native(val ty: AugType) : QualName()

        companion object {
            val nameMap = mapOf(
                "Item Quantity" to Native(AugType.Generic),
                "Item Rarity" to Native(AugType.Rarity),
                "Monster Pack Size" to Native(AugType.Pack),
                "More Currency" to Native(AugType.Currency),
                "More Divination Cards" to Native(AugType.DivCard),
                "More Maps" to Native(AugType.Map),
                "More Scarabs" to Native(AugType.Scarab),
                "Quality" to FromCurrency(AugType.Generic),
                "Quality (Rarity)" to FromCurrency(AugType.Rarity),
                "Quality (Pack Size)" to FromCurrency(AugType.Pack),
                "Quality (Currency)" to FromCurrency(AugType.Currency),
                "Quality (Divination Cards)" to FromCurrency(AugType.DivCard),
                "Quality (Maps)" to FromCurrency(AugType.Map),
                "Quality (Scarabs)" to FromCurrency(AugType.Scarab),
            )

            fun fromName(name: String) = nameMap[name]
        }
    }

    enum class AugType {
        Generic,
        Rarity, Pack, Map, Currency, Scarab, DivCard,
    }
}

fun PoeRollableItem.getAffix(name: String): PoeRollableItem.ExplicitMod? {
    return explicitMods.firstOrNull { it.name == name }
}

fun PoeRollableItem.hasAffix(name: String): Boolean {
    return getAffix(name) != null
}

fun PoeRollableItem.hasAffixThat(
    predicate: (PoeRollableItem.ExplicitMod) -> Boolean,
): Boolean {
    return explicitMods.any(predicate)
}
