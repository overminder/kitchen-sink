package macrocore

import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class MapModDatabaseTest {

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

    @Nested
    inner class ModMatching {
        @Test
        fun `finds volatile cores descriptor`() {
            val mod = PoeRollableItem.ExplicitMod(
                loc = PoeRollableItem.ExplicitModLocation.Prefix,
                name = "Volatile",
                tier = 1,
                description = "Rare Monsters have Volatile Cores",
            )
            val descriptor = findMatchingDescriptor(mod)
            assertThat(descriptor).isEqualTo(T17Mods.volatile)
        }

        @Test
        fun `finds stalwart descriptor`() {
            val mod = PoeRollableItem.ExplicitMod(
                loc = PoeRollableItem.ExplicitModLocation.Prefix,
                name = "Stalwart",
                tier = 1,
                description = "Monsters have +50% Chance to Block Attack Damage",
            )
            val descriptor = findMatchingDescriptor(mod)
            assertThat(descriptor).isEqualTo(T17Mods.stalwart)
        }

        @Test
        fun `finds frenzy charge on hit`() {
            val mod = PoeRollableItem.ExplicitMod(
                loc = PoeRollableItem.ExplicitModLocation.Suffix,
                name = "of Frenzy",
                tier = null,
                description = "Monsters gain a Frenzy Charge on Hit",
            )
            val descriptor = findMatchingDescriptor(mod)
            assertThat(descriptor).isEqualTo(T16Mods.ofFrenzy)
        }

        @Test
        fun `finds exposure descriptor`() {
            val mod = PoeRollableItem.ExplicitMod(
                loc = PoeRollableItem.ExplicitModLocation.Suffix,
                name = "of Exposure",
                tier = 1,
                description = "Players have -20% to all maximum Resistances",
            )
            val descriptor = findMatchingDescriptor(mod)
            assertThat(descriptor).isEqualTo(T16Mods.ofExposure)
        }
    }

    @Nested
    inner class VariableExtraction {
        @Test
        fun `extracts variable from fecund mod`() {
            val mod = PoeRollableItem.ExplicitMod(
                loc = PoeRollableItem.ExplicitModLocation.Prefix,
                name = "Fecund",
                tier = 3,
                description = "55% more Monster Life",
            )
            val variable = getVariableForMod(mod, 0)
            assertThat(variable).isEqualTo(55)
        }

        @Test
        fun `extracts negative variable from exposure mod`() {
            val mod = PoeRollableItem.ExplicitMod(
                loc = PoeRollableItem.ExplicitModLocation.Suffix,
                name = "of Exposure",
                tier = 1,
                description = "Players have -20% to all maximum Resistances",
            )
            val variable = getVariableForMod(mod, 0)
            assertThat(variable).isEqualTo(-20)
        }

        @Test
        fun `extracts second variable from multi-variable mod`() {
            val mod = PoeRollableItem.ExplicitMod(
                loc = PoeRollableItem.ExplicitModLocation.Suffix,
                name = "of Deadliness",
                tier = 1,
                description = "Monsters have 300% increased Critical Strike Chance; +75% to Monster Critical Strike Multiplier",
            )
            val variable = getVariableForMod(mod, 1)
            assertThat(variable).isEqualTo(75)
        }
    }

    @Nested
    inner class DifficultyCalculation {
        @Test
        fun `calculates difficulty for parsed T17 map`() {
            val item = PoeItemParser.parseAsRollable(t17MapDescription)
            val difficulty = getMapDifficulty(item)
            // Should have non-trivial difficulty given the mods
            assertThat(difficulty.playerDamageTaken).isGreaterThan(1.0)
            assertThat(difficulty.monsterEhp).isGreaterThanOrEqualTo(1.0)
        }

        @Test
        fun `simple fecund mod increases monster EHP`() {
            val item = PoeRollableItem(
                klass = PoeItem.Map(PoeItem.MapTier.Other),
                rarity = PoeRollableItem.Rarity.Rare,
                explicitMods = listOf(
                    PoeRollableItem.ExplicitMod(
                        loc = PoeRollableItem.ExplicitModLocation.Prefix,
                        name = "Fecund",
                        tier = 3,
                        description = "55% more Monster Life",
                    )
                ),
                qualities = emptyList(),
                originalDescription = "",
            )
            val difficulty = getMapDifficulty(item)
            // 55% * 1.56 atlas multi = 85.8% more monster HP
            assertThat(difficulty.monsterEhp).isGreaterThan(1.5)
            assertThat(difficulty.playerDamageTaken).isEqualTo(1.0)
        }
    }

    @Nested
    inner class BadModDetection {
        @Test
        fun `detects cycling as bad mod`() {
            val item = PoeRollableItem(
                klass = PoeItem.Map(PoeItem.MapTier.T17),
                rarity = PoeRollableItem.Rarity.Rare,
                explicitMods = listOf(
                    PoeRollableItem.ExplicitMod(
                        loc = PoeRollableItem.ExplicitModLocation.Prefix,
                        name = "Cycling",
                        tier = 1,
                        description = "Players and their Minions deal no damage for 3 out of every 10 seconds",
                    )
                ),
                qualities = emptyList(),
                originalDescription = "",
            )
            val badMods = PoeMapMods.getBadMods(item)
            assertThat(badMods).hasSize(1)
            assertThat(badMods[0].name).isEqualTo("Cycling")
        }

        @Test
        fun `does not flag normal mods as bad`() {
            val item = PoeRollableItem(
                klass = PoeItem.Map(PoeItem.MapTier.T17),
                rarity = PoeRollableItem.Rarity.Rare,
                explicitMods = listOf(
                    PoeRollableItem.ExplicitMod(
                        loc = PoeRollableItem.ExplicitModLocation.Prefix,
                        name = "Stalwart",
                        tier = 1,
                        description = "Monsters have +50% Chance to Block Attack Damage",
                    )
                ),
                qualities = emptyList(),
                originalDescription = "",
            )
            val badMods = PoeMapMods.getBadMods(item)
            assertThat(badMods).isEmpty()
        }

        @Test
        fun `detects volatile + exposure combo as bad`() {
            val item = PoeRollableItem(
                klass = PoeItem.Map(PoeItem.MapTier.T17),
                rarity = PoeRollableItem.Rarity.Rare,
                explicitMods = listOf(
                    PoeRollableItem.ExplicitMod(
                        loc = PoeRollableItem.ExplicitModLocation.Prefix,
                        name = "Volatile",
                        tier = 1,
                        description = "Rare Monsters have Volatile Cores",
                    ),
                    PoeRollableItem.ExplicitMod(
                        loc = PoeRollableItem.ExplicitModLocation.Suffix,
                        name = "of Exposure",
                        tier = 1,
                        description = "Players have -20% to all maximum Resistances",
                    ),
                ),
                qualities = emptyList(),
                originalDescription = "",
            )
            val badMods = PoeMapMods.getBadMods(item)
            assertThat(badMods).hasSize(2)
        }
    }

    @Nested
    inner class PoeMapDifficultyTests {
        @Test
        fun `strictlyLessOrEqualTo works correctly`() {
            val easy = PoeMapDifficulty(2.0, 3.0)
            val hard = PoeMapDifficulty(4.0, 6.0)
            assertThat(easy.strictlyLessOrEqualTo(hard)).isTrue()
            assertThat(hard.strictlyLessOrEqualTo(easy)).isFalse()
            assertThat(easy.strictlyLessOrEqualTo(easy)).isTrue()
        }

        @Test
        fun `times operator scales both axes`() {
            val d = PoeMapDifficulty(2.0, 3.0)
            val scaled = d * 2.0
            assertThat(scaled.playerDamageTaken).isEqualTo(4.0)
            assertThat(scaled.monsterEhp).isEqualTo(6.0)
        }
    }

    @Nested
    inner class ModCoverage {
        @Test
        fun `T16 ALL list is not empty`() {
            assertThat(T16Mods.ALL).isNotEmpty()
        }

        @Test
        fun `T17 ALL list is not empty`() {
            assertThat(T17Mods.ALL).isNotEmpty()
        }

        @Test
        fun `PoeMapMods ALL combines both`() {
            assertThat(PoeMapMods.ALL.size).isEqualTo(T17Mods.ALL.size + T16Mods.ALL.size)
        }
    }
}
