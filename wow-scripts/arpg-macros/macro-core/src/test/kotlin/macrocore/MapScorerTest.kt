package macrocore

import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class MapScorerTest {

    private val goodT17Map = PoeItemParser.parseAsRollable("""
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
{ Prefix Modifier "Stalwart" (Tier: 1) }
Monsters have +50% Chance to Block Attack Damage

{ Suffix Modifier "of Splinters" (Tier: 1) }
25% chance for Rare Monsters to Fracture on death

--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
    """.trimIndent())

    private val badT17Map = PoeItemParser.parseAsRollable("""
Item Class: Maps
Rarity: Rare
Doom Vortex
Fortress Map
--------
Map Tier: 17
Item Quantity: +30% (augmented)
Monster Pack Size: +10% (augmented)
--------
Item Level: 84
--------
{ Prefix Modifier "Cycling" (Tier: 1) }
Players and their Minions deal no damage for 3 out of every 10 seconds

{ Suffix Modifier "of Frenzy" }
Monsters gain a Frenzy Charge on Hit

--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
    """.trimIndent())

    @Nested
    inner class ScarabScorer {
        @Test
        fun `good map scores above threshold`() {
            val output = MapScorerImpl.SCARAB.evaluate(goodT17Map)
            assertThat(output.score).isGreaterThan(output.scoreThreshold)
            assertThat(output.isGood).isTrue()
        }

        @Test
        fun `bad map has bad mods`() {
            val output = MapScorerImpl.SCARAB.evaluate(badT17Map)
            assertThat(output.badMods).isNotEmpty()
            assertThat(output.isGood).isFalse()
        }
    }

    @Nested
    inner class ScorerOutput {
        @Test
        fun `isGood requires score above threshold`() {
            val output = MapScorerOutput(
                scorerName = "test",
                score = 5.0,
                scoreThreshold = 10.0,
                difficulty = PoeMapDifficulty(1.0, 1.0),
                easyEnough = true,
                badMods = emptyList(),
            )
            assertThat(output.isGood).isFalse()
        }

        @Test
        fun `isGood requires easyEnough`() {
            val output = MapScorerOutput(
                scorerName = "test",
                score = 15.0,
                scoreThreshold = 10.0,
                difficulty = PoeMapDifficulty(100.0, 100.0),
                easyEnough = false,
                badMods = emptyList(),
            )
            assertThat(output.isGood).isFalse()
        }

        @Test
        fun `isGood requires no bad mods`() {
            val output = MapScorerOutput(
                scorerName = "test",
                score = 15.0,
                scoreThreshold = 10.0,
                difficulty = PoeMapDifficulty(1.0, 1.0),
                easyEnough = true,
                badMods = listOf(
                    PoeRollableItem.ExplicitMod(
                        PoeRollableItem.ExplicitModLocation.Prefix,
                        "Cycling", 1, "bad mod"
                    )
                ),
            )
            assertThat(output.isGood).isFalse()
        }

        @Test
        fun `isGood when all criteria pass`() {
            val output = MapScorerOutput(
                scorerName = "test",
                score = 15.0,
                scoreThreshold = 10.0,
                difficulty = PoeMapDifficulty(1.0, 1.0),
                easyEnough = true,
                badMods = emptyList(),
            )
            assertThat(output.isGood).isTrue()
        }
    }

    @Nested
    inner class BestOfScorer {
        @Test
        fun `picks scorer with best relative score`() {
            val alwaysLow = object : MapScorer {
                override fun evaluate(item: PoeRollableItem) = MapScorerOutput(
                    "low", 1.0, 10.0, PoeMapDifficulty(1.0, 1.0), true, emptyList()
                )
            }
            val alwaysHigh = object : MapScorer {
                override fun evaluate(item: PoeRollableItem) = MapScorerOutput(
                    "high", 20.0, 10.0, PoeMapDifficulty(1.0, 1.0), true, emptyList()
                )
            }
            val best = MapScorer.bestOf(listOf(alwaysLow, alwaysHigh))
            val result = best.evaluate(goodT17Map)
            assertThat(result.scorerName).isEqualTo("high")
        }
    }

    @Nested
    inner class ScarabOrMapScorer {
        @Test
        fun `uses scarab scorer for T17`() {
            val result = MapScorerImpl.SCARAB_OR_MAP.evaluate(goodT17Map)
            assertThat(result.scorerName).isEqualTo("scarab")
        }
    }

    @Nested
    inner class ReportGeneration {
        @Test
        fun `generates report string`() {
            val output = MapScorerOutput(
                scorerName = "scarab",
                score = 7.5,
                scoreThreshold = 6.8,
                difficulty = PoeMapDifficulty(2.0, 1.5),
                easyEnough = true,
                badMods = emptyList(),
            )
            val report = generateMapReport(listOf(output))
            assertThat(report).contains("Average score")
            assertThat(report).contains("scarab")
        }
    }
}
