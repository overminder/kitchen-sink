package com.gh.om.ks.arpgmacro.core

import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class PoeItemParserTest {

    @Nested
    inner class MapParsing {
        private val t17MapDescription = """
Item Class: Maps
Rarity: Rare
Ancient Trap
Fortress Map
--------
Map Tier: 17
Item Quantity: +110% (augmented)
Item Rarity: +54% (augmented)
Monster Pack Size: +40% (augmented)
More Scarabs: +78% (augmented)
More Currency: +140% (augmented)
Quality: +20% (augmented)
--------
Item Level: 84
--------
Monster Level: 84
--------
Delirium Reward Type: Weapons (enchant)
Players in Area are 20% Delirious (enchant)
--------
{ Prefix Modifier "Volatile" (Tier: 1) }
Rare Monsters have Volatile Cores

{ Prefix Modifier "Stalwart" (Tier: 1) }
Monsters have +50% Chance to Block Attack Damage

{ Prefix Modifier "Retributive" (Tier: 1) }
Players are Marked for Death for 10 seconds
after killing a Rare or Unique monster
(Players that are Marked for Death take 50% increased Damage)

{ Suffix Modifier "of Exposure" (Tier: 1) }
Players have -20% to all maximum Resistances

{ Suffix Modifier "of Temporal Chains" — Caster, Curse }
Players are Cursed with Temporal Chains
(Temporal Chains is a Hex which reduces Action Speed by 15%, or 9% on Rare or Unique targets, and makes other effects on the target expire 40% slower. It has 50% less effect on Players and lasts 5 seconds)

{ Suffix Modifier "of Splinters" (Tier: 1) }
25% chance for Rare Monsters to Fracture on death

--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
--------
Modifiable only with Chaos Orbs, Vaal Orbs, Delirium Orbs and Chisels
        """.trimIndent()

        @Test
        fun `parses T17 map class`() {
            val item = PoeItemParser.parseAsRollable(t17MapDescription)
            assertThat(item.klass).isEqualTo(PoeItem.Map(PoeItem.MapTier.T17))
        }

        @Test
        fun `parses rarity`() {
            val item = PoeItemParser.parseAsRollable(t17MapDescription)
            assertThat(item.rarity).isEqualTo(PoeRollableItem.Rarity.Rare)
        }

        @Test
        fun `parses explicit mods`() {
            val item = PoeItemParser.parseAsRollable(t17MapDescription)
            assertThat(item.explicitMods).hasSize(6)
            assertThat(item.explicitMods[0].name).isEqualTo("Volatile")
            assertThat(item.explicitMods[0].tier).isEqualTo(1)
            assertThat(item.explicitMods[0].loc).isEqualTo(PoeRollableItem.ExplicitModLocation.Prefix)
        }

        @Test
        fun `parses suffix mods`() {
            val item = PoeItemParser.parseAsRollable(t17MapDescription)
            val suffixes = item.explicitMods.filter {
                it.loc == PoeRollableItem.ExplicitModLocation.Suffix
            }
            assertThat(suffixes).hasSize(3)
            assertThat(suffixes.map { it.name }).containsExactly(
                "of Exposure", "of Temporal Chains", "of Splinters"
            )
        }

        @Test
        fun `parses mod without tier`() {
            val item = PoeItemParser.parseAsRollable(t17MapDescription)
            val tempChains = item.explicitMods.first { it.name == "of Temporal Chains" }
            assertThat(tempChains.tier).isNull()
        }

        @Test
        fun `parses qualities`() {
            val item = PoeItemParser.parseAsRollable(t17MapDescription)
            val quant = item.qualities.first {
                it.name == PoeRollableItem.QualName.Native(PoeRollableItem.AugType.Generic)
            }
            assertThat(quant.value).isEqualTo(110)

            val scarab = item.qualities.first {
                it.name == PoeRollableItem.QualName.Native(PoeRollableItem.AugType.Scarab)
            }
            assertThat(scarab.value).isEqualTo(78)

            val currency = item.qualities.first {
                it.name == PoeRollableItem.QualName.Native(PoeRollableItem.AugType.Currency)
            }
            assertThat(currency.value).isEqualTo(140)
        }

        @Test
        fun `parses chisel quality`() {
            val item = PoeItemParser.parseAsRollable(t17MapDescription)
            val chiselQual = item.qualities.first {
                it.name is PoeRollableItem.QualName.FromCurrency
            }
            assertThat(chiselQual.value).isEqualTo(20)
            assertThat(chiselQual.name).isEqualTo(
                PoeRollableItem.QualName.FromCurrency(PoeRollableItem.AugType.Generic)
            )
        }

        @Test
        fun `parses pack size`() {
            val item = PoeItemParser.parseAsRollable(t17MapDescription)
            val pack = item.qualities.first {
                it.name == PoeRollableItem.QualName.Native(PoeRollableItem.AugType.Pack)
            }
            assertThat(pack.value).isEqualTo(40)
        }
    }

    @Nested
    inner class OriginatorMapParsing {
        private val t16_5MapDescription = """
Item Class: Maps
Rarity: Rare
Woe Vortex
Crimson Temple Map
--------
Map Tier: 16
Item Quantity: +95% (augmented)
Item Rarity: +48% (augmented)
Monster Pack Size: +32% (augmented)
More Maps: +60% (augmented)
Quality (Pack Size): +4%
--------
Item Level: 83
--------
Monster Level: 83
--------
Area is Influenced by the Originator's Memories
--------
{ Prefix Modifier "Fecund" (Tier: 3) }
55% more Monster Life

{ Prefix Modifier "Savage" (Tier: 2) }
30% increased Monster Damage

{ Suffix Modifier "of Frenzy" }
Monsters gain a Frenzy Charge on Hit

--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
        """.trimIndent()

        @Test
        fun `parses T16_5 originator map`() {
            val item = PoeItemParser.parseAsRollable(t16_5MapDescription)
            assertThat(item.klass).isEqualTo(PoeItem.Map(PoeItem.MapTier.T16_5))
        }

        @Test
        fun `parses qualities including chisel pack size`() {
            val item = PoeItemParser.parseAsRollable(t16_5MapDescription)
            val chiselPack = item.qualities.first {
                it.name == PoeRollableItem.QualName.FromCurrency(PoeRollableItem.AugType.Pack)
            }
            assertThat(chiselPack.value).isEqualTo(4)
        }

        @Test
        fun `parses map drop quality`() {
            val item = PoeItemParser.parseAsRollable(t16_5MapDescription)
            val mapDrop = item.qualities.first {
                it.name == PoeRollableItem.QualName.Native(PoeRollableItem.AugType.Map)
            }
            assertThat(mapDrop.value).isEqualTo(60)
        }
    }

    @Nested
    inner class RegularMapParsing {
        private val regularMap = """
Item Class: Maps
Rarity: Normal
Mesa Map
--------
Map Tier: 14
--------
Item Level: 81
--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
        """.trimIndent()

        @Test
        fun `parses normal rarity map`() {
            val item = PoeItemParser.parseAsRollable(regularMap)
            assertThat(item.rarity).isEqualTo(PoeRollableItem.Rarity.Normal)
            assertThat(item.klass).isEqualTo(PoeItem.Map(PoeItem.MapTier.Other))
        }

        @Test
        fun `normal map has no explicit mods`() {
            val item = PoeItemParser.parseAsRollable(regularMap)
            assertThat(item.explicitMods).isEmpty()
        }
    }

    @Nested
    inner class CurrencyParsing {
        private val chaosOrb = """
Item Class: Stackable Currency
Rarity: Currency
Chaos Orb
--------
Stack Size: 47/20
--------
Reforges a rare item with new random modifiers
--------
Right click this item then left click a rare item to apply it.
Shift click to unstack.
        """.trimIndent()

        @Test
        fun `parses chaos orb currency`() {
            val item = PoeItemParser.parse(chaosOrb)
            assertThat(item).isInstanceOf(PoeCurrency::class.java)
            val currency = item as PoeCurrency
            assertThat(currency.type).isEqualTo(PoeCurrency.ChaosType)
            assertThat(currency.stackSize).isEqualTo(47)
        }

        private val unknownCurrency = """
Item Class: Stackable Currency
Rarity: Currency
Orb of Chance
--------
Stack Size: 123/20
--------
Upgrades a normal item to a random rarity
        """.trimIndent()

        @Test
        fun `parses unknown currency type`() {
            val item = PoeItemParser.parse(unknownCurrency)
            assertThat(item).isInstanceOf(PoeCurrency::class.java)
            val currency = item as PoeCurrency
            assertThat(currency.type).isInstanceOf(PoeCurrency.UnknownType::class.java)
            assertThat(currency.stackSize).isEqualTo(123)
        }
    }

    @Nested
    inner class ItemHelpers {
        @Test
        fun `isMapLike returns true for map classes`() {
            assertThat(PoeItem.ConstKlass.Map.isMapLike()).isTrue()
            assertThat(PoeItem.ConstKlass.MiscMap.isMapLike()).isTrue()
            assertThat(PoeItem.Map(PoeItem.MapTier.T17).isMapLike()).isTrue()
        }

        @Test
        fun `isMapLike returns false for non-map classes`() {
            assertThat(PoeItem.ConstKlass.Currency.isMapLike()).isFalse()
            assertThat(PoeItem.ConstKlass.Jewels.isMapLike()).isFalse()
            assertThat((null as PoeItem.Klass?).isMapLike()).isFalse()
        }

        @Test
        fun `hasAffix finds matching affix`() {
            val item = PoeRollableItem(
                klass = PoeItem.Map(PoeItem.MapTier.T17),
                rarity = PoeRollableItem.Rarity.Rare,
                explicitMods = listOf(
                    PoeRollableItem.ExplicitMod(
                        loc = PoeRollableItem.ExplicitModLocation.Prefix,
                        name = "Volatile",
                        tier = 1,
                        description = "Rare Monsters have Volatile Cores",
                    )
                ),
                qualities = emptyList(),
                originalDescription = "",
            )
            assertThat(item.hasAffix("Volatile")).isTrue()
            assertThat(item.hasAffix("Nonexistent")).isFalse()
        }
    }

    @Nested
    inner class MultiLineModParsing {
        private val multiLineMod = """
Item Class: Maps
Rarity: Rare
Test Map
Strand Map
--------
Map Tier: 17
Item Quantity: +80% (augmented)
Monster Pack Size: +25% (augmented)
--------
Item Level: 84
--------
{ Prefix Modifier "Retributive" (Tier: 1) }
Players are Marked for Death for 10 seconds
after killing a Rare or Unique monster
(Players that are Marked for Death take 50% increased Damage)

{ Suffix Modifier "of Power" }
Monsters gain a Power Charge on Hit

--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
        """.trimIndent()

        @Test
        fun `handles multi-line mod descriptions`() {
            val item = PoeItemParser.parseAsRollable(multiLineMod)
            assertThat(item.explicitMods).hasSize(2)
            val retributive = item.explicitMods[0]
            assertThat(retributive.name).isEqualTo("Retributive")
            // The multi-line description should be joined with "; "
            assertThat(retributive.description).contains("Players are Marked for Death")
            assertThat(retributive.description).contains("after killing a Rare or Unique monster")
        }
    }
}
