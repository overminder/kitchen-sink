package com.gh.om.ks.arpgmacro.core.item

import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem.ExplicitMod.Matcher
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem.ExplicitModLocation

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
        // POE2
        Waystone("Waystones"),
        Tablet("Tablet"),
    }

    enum class MapTier {
        Other,
        T16_5,
        T17,
    }

    data class Map(val tier: MapTier) : Klass

    sealed interface Equipment : Klass
    // There are a lot of weapon classes, and I'm not listing them all (yet).
    data class Weapon(val kind: String) : Equipment

    enum class NonWeapon(val repr: String) : Equipment {
        Body("Body Armours"),
        Helm("Helmets"),
        Shield("Shields"),
        Gloves("Gloves"),
        Boots("Boots"),
        Belt("Belts"),
        Ring("Rings"),
        Amulet("Amulets");

        companion object {
            fun fromRepr(repr: String): NonWeapon? {
                return entries.firstOrNull { it.repr == repr }
            }
        }
    }
}

fun PoeItem.Klass?.isMapLike(): Boolean {
    return when (this) {
        PoeItem.ConstKlass.Map,
        PoeItem.ConstKlass.MiscMap,
        PoeItem.ConstKlass.Waystone,
        is PoeItem.Map -> true
        else -> false
    }
}

data class PoeCurrency(
    val type: Type,
    val stackSize: Int,
) : PoeItem {
    sealed interface Type

    sealed interface KnownType : Type

    enum class Simple(val repr: String) : KnownType {
        Scour("Orb of Scouring"),
        Alch("Orb of Alchemy"),
        Binding("Orb of Binding"),
        Annul("Orb of Annulment"),
    }

    /**
     * Some POE2 currencies have tiers.
     */
    enum class Tier(val repr: String) {
        Greater("Greater"),
        Perfect("Perfect"),
    }

    enum class CanHaveTier(val repr: String) {
        Trans("Orb of Transmutation"),
        Aug("Orb of Augmentation"),
        Regal("Regal Orb"),
        Exalt("Exalted Orb"),
        Chaos("Chaos Orb"),
    }

    data class TieredType(val kind: CanHaveTier, val tier: Tier? = null) : KnownType {
        fun asNormal() = TieredType(kind)
        fun asGreater() = TieredType(kind, Tier.Greater)
        fun asPerfect() = TieredType(kind, Tier.Perfect)
    }

    data class UnknownType(val repr: String) : Type

    companion object {
        val Chaos = TieredType(CanHaveTier.Chaos)
        val Trans = TieredType(CanHaveTier.Trans)
        val Aug = TieredType(CanHaveTier.Aug)
        val Regal = TieredType(CanHaveTier.Regal)
        val Exalt = TieredType(CanHaveTier.Exalt)
        val Annul = Simple.Annul
    }
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
        Unique;

        fun isAtMost(rarity: Rarity): Boolean {
            return this <= rarity
        }
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
        val fractured: Boolean = false,
    ) {
        interface Matcher {
            fun matches(mod: ExplicitMod): Boolean

            /**
             * The location of the affix matched by this matcher.
             * Null if the location is unknown.
             */
            val loc: ExplicitModLocation?
                get() = null

            companion object {
                fun byPredicate(predicate: (ExplicitMod) -> Boolean): Matcher {
                    return object: Matcher {
                        override fun matches(mod: ExplicitMod) = predicate(mod)
                    }
                }

                fun byName(name: String): Matcher {
                    // TODO consider a better toString or just use data classes.
                    val m = byPredicate {
                        it.name == name
                    }

                    // Guess the location (should usually work?)
                    return if (name.startsWith("of ")) {
                        m.asSuffix()
                    } else {
                        m.asPrefix()
                    }
                }

                fun byAnyNames(names: List<String>) = byPredicate {
                    it.name in names
                }

                fun containsDescription(descr: String) = byPredicate {
                    descr in it.description
                }
            }
        }
    }

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

fun PoeRollableItem.affixThat(
    predicate: (PoeRollableItem.ExplicitMod) -> Boolean,
): List<PoeRollableItem.ExplicitMod> = explicitMods.filter(predicate)

fun PoeRollableItem.hasAffixThat(
    predicate: (PoeRollableItem.ExplicitMod) -> Boolean,
): Boolean {
    return explicitMods.any(predicate)
}

fun Matcher.withLoc(newLoc: ExplicitModLocation) = object: Matcher by this {
    override val loc = newLoc
}

fun Matcher.asPrefix() = withLoc(ExplicitModLocation.Prefix)
fun Matcher.asSuffix() = withLoc(ExplicitModLocation.Suffix)

val PoeRollableItem.ExplicitMod.isPrefix
    get() = loc == ExplicitModLocation.Prefix

val PoeRollableItem.ExplicitMod.isSuffix
    get() = loc == ExplicitModLocation.Suffix

