package com.gh.om.ks.arpgmacro.core

import com.gh.om.ks.arpgmacro.core.CraftDecisionMaker.DecisionType
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class CraftDecisionMakerTest {

    private fun mod(
        name: String,
        loc: PoeRollableItem.ExplicitModLocation = PoeRollableItem.ExplicitModLocation.Prefix,
        tier: Int? = null,
        description: String = "",
    ) = PoeRollableItem.ExplicitMod(loc = loc, name = name, tier = tier, description = description)

    private fun item(
        vararg mods: PoeRollableItem.ExplicitMod,
        rarity: PoeRollableItem.Rarity = PoeRollableItem.Rarity.Magic,
    ) = PoeRollableItem(
        klass = PoeItem.ConstKlass.Jewels,
        rarity = rarity,
        explicitMods = mods.toList(),
        qualities = emptyList(),
        originalDescription = "",
    )

    @Nested
    inner class ByMatches {
        @Test
        fun `done when matches meets desired count`() {
            val d = CraftDecisionMaker.byMatches(matches = 3, desiredModCount = 3, nMods = 4)
            assertThat(d.type).isEqualTo(DecisionType.Done)
            assertThat(d.isGood).isTrue()
        }

        @Test
        fun `done when matches exceeds desired count`() {
            val d = CraftDecisionMaker.byMatches(matches = 4, desiredModCount = 3, nMods = 4)
            assertThat(d.type).isEqualTo(DecisionType.Done)
        }

        @Test
        fun `proceed when all mods match but not enough yet`() {
            val d = CraftDecisionMaker.byMatches(matches = 2, desiredModCount = 3, nMods = 2)
            assertThat(d.type).isEqualTo(DecisionType.Proceed)
        }

        @Test
        fun `go back when 3 of 4 match`() {
            val d = CraftDecisionMaker.byMatches(matches = 3, desiredModCount = 4, nMods = 4)
            assertThat(d.type).isEqualTo(DecisionType.GoBack)
        }

        @Test
        fun `reset when too few matches`() {
            val d = CraftDecisionMaker.byMatches(matches = 1, desiredModCount = 3, nMods = 3)
            assertThat(d.type).isEqualTo(DecisionType.Reset)
        }

        @Test
        fun `reset when 0 matches`() {
            val d = CraftDecisionMaker.byMatches(matches = 0, desiredModCount = 2, nMods = 2)
            assertThat(d.type).isEqualTo(DecisionType.Reset)
        }

        @Test
        fun `go back only triggers at exactly 4 mods`() {
            // 2 of 3 match, nMods = 3 -> not GoBack (nMods != 4)
            val d = CraftDecisionMaker.byMatches(matches = 2, desiredModCount = 3, nMods = 3)
            assertThat(d.type).isEqualTo(DecisionType.Reset)
        }
    }

    @Nested
    inner class ByDesiredModsEx {
        private val dm = CraftDecisionMaker.byDesiredMods(
            desiredModNames = listOf("Alpha", "Beta", "Gamma"),
            desiredModCount = 2,
        )

        @Test
        fun `done when enough mods match by name`() {
            val d = dm.getDecision(item(mod("Alpha"), mod("Beta")))
            assertThat(d.type).isEqualTo(DecisionType.Done)
        }

        @Test
        fun `proceed when all current mods match but need more`() {
            val d = dm.getDecision(item(mod("Alpha")))
            assertThat(d.type).isEqualTo(DecisionType.Proceed)
        }

        @Test
        fun `reset when mod does not match`() {
            val d = dm.getDecision(item(mod("Alpha"), mod("Zeta")))
            assertThat(d.type).isEqualTo(DecisionType.Reset)
        }
    }

    @Nested
    inner class ByDesiredOneSideModsEx {
        private val dm = CraftDecisionMaker.byDesiredOneSideMods(
            desiredModNames = listOf("Alpha", "Beta"),
            side = PoeRollableItem.ExplicitModLocation.Prefix,
            desiredModCount = 2,
        )

        @Test
        fun `done when enough prefix mods match`() {
            val d = dm.getDecision(item(
                mod("Alpha", loc = PoeRollableItem.ExplicitModLocation.Prefix),
                mod("Beta", loc = PoeRollableItem.ExplicitModLocation.Prefix),
            ))
            assertThat(d.type).isEqualTo(DecisionType.Done)
        }

        @Test
        fun `ignores suffix mods`() {
            val d = dm.getDecision(item(
                mod("Alpha", loc = PoeRollableItem.ExplicitModLocation.Prefix),
                mod("Beta", loc = PoeRollableItem.ExplicitModLocation.Suffix),
            ))
            assertThat(d.type).isEqualTo(DecisionType.Proceed)
        }

        @Test
        fun `forces reset on rare when prefix mods insufficient`() {
            val d = dm.getDecision(item(
                mod("Alpha", loc = PoeRollableItem.ExplicitModLocation.Prefix),
                mod("Zeta", loc = PoeRollableItem.ExplicitModLocation.Suffix),
                rarity = PoeRollableItem.Rarity.Rare,
            ))
            assertThat(d.type).isEqualTo(DecisionType.Reset)
            assertThat(d.why).contains("after regal")
        }

        @Test
        fun `does not force reset on magic`() {
            val d = dm.getDecision(item(
                mod("Alpha", loc = PoeRollableItem.ExplicitModLocation.Prefix),
                rarity = PoeRollableItem.Rarity.Magic,
            ))
            assertThat(d.type).isEqualTo(DecisionType.Proceed)
        }
    }

    @Nested
    inner class ByDesiredOneSideModsWithExtraCheck {
        private val dm = CraftDecisionMaker.byDesiredOneSideMods(
            desiredModNames = listOf("Alpha"),
            side = PoeRollableItem.ExplicitModLocation.Suffix,
            desiredModCount = 1,
            extraCheck = { "+22" in it.description },
        )

        @Test
        fun `matches when name and extra check pass`() {
            val d = dm.getDecision(item(
                mod("Alpha", loc = PoeRollableItem.ExplicitModLocation.Suffix, description = "+22% to something"),
            ))
            assertThat(d.type).isEqualTo(DecisionType.Done)
        }

        @Test
        fun `rejects when extra check fails`() {
            val d = dm.getDecision(item(
                mod("Alpha", loc = PoeRollableItem.ExplicitModLocation.Suffix, description = "+18% to something"),
            ))
            assertThat(d.type).isEqualTo(DecisionType.Reset)
        }
    }

    @Nested
    inner class AsItemChecker {
        @Test
        fun `bridges to ItemChecker interface`() {
            val dm = CraftDecisionMaker.byDesiredMods(listOf("Alpha"), 1)
            val checker = dm.asItemChecker()

            val good = item(mod("Alpha"))
            val bad = item(mod("Zeta"))

            assertThat(checker.evaluate(good).isGood).isTrue()
            assertThat(checker.evaluate(bad).isGood).isFalse()
            assertThat(checker.generateReport(listOf())).isEqualTo("Ok")
        }
    }

    @Nested
    inner class MatchesDescription {
        @Test
        fun `matches when description contains keyword`() {
            val m = mod("Test", description = "1 Added Passive Skill is Grand Design")
            assertThat(CraftDecisionMaker.matchesDescription(m, listOf("Grand Design"))).isTrue()
        }

        @Test
        fun `no match when description lacks keyword`() {
            val m = mod("Test", description = "Some other description")
            assertThat(CraftDecisionMaker.matchesDescription(m, listOf("Grand Design"))).isFalse()
        }
    }
}
