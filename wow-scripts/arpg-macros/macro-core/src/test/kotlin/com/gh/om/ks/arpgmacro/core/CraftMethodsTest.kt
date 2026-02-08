package com.gh.om.ks.arpgmacro.core

import kotlinx.coroutines.test.runTest
import com.gh.om.ks.arpgmacro.core.CraftDecisionMaker.DecisionType
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class CraftMethodsTest {

    /** Records which currency methods were called in order. */
    private class RecordingCrafter(
        private var currentItem: PoeRollableItem,
    ) : PoeItemCrafter {
        val calls = mutableListOf<String>()

        override suspend fun getCurrentItem() = currentItem

        override suspend fun transmute() { calls += "transmute" }
        override suspend fun alternate() { calls += "alternate" }
        override suspend fun augment() { calls += "augment" }
        override suspend fun regal() { calls += "regal" }
        override suspend fun exalt() { calls += "exalt" }
        override suspend fun scour() { calls += "scour" }
        override suspend fun annul() { calls += "annul" }
        override suspend fun chaos() { calls += "chaos" }
        override suspend fun alch() { calls += "alch" }
        override suspend fun armourerScrap() { calls += "armourerScrap" }
        override suspend fun whetstone() { calls += "whetstone" }
    }

    private fun mod(
        name: String,
        loc: PoeRollableItem.ExplicitModLocation = PoeRollableItem.ExplicitModLocation.Prefix,
    ) = PoeRollableItem.ExplicitMod(loc = loc, name = name, tier = null, description = "")

    private fun item(
        rarity: PoeRollableItem.Rarity,
        vararg mods: PoeRollableItem.ExplicitMod,
        originalDescription: String = "",
    ) = PoeRollableItem(
        klass = PoeItem.ConstKlass.Jewels,
        rarity = rarity,
        explicitMods = mods.toList(),
        qualities = emptyList(),
        originalDescription = originalDescription,
    )

    /** Always returns a specific decision type. */
    private fun fixedDm(type: DecisionType) = CraftDecisionMaker { _ ->
        CraftDecisionMaker.Decision(type, "test")
    }

    @Nested
    inner class AltAugRegalExaltOnce {
        @Test
        fun `done returns immediately without applying currency`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Magic, mod("A")))
            val result = CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Done))
            assertThat(result.done).isTrue()
            assertThat(crafter.calls).isEmpty()
        }

        @Test
        fun `normal item gets transmuted`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Normal))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("transmute")
        }

        @Test
        fun `normal heist base gets alched`() = runTest {
            val crafter = RecordingCrafter(item(
                PoeRollableItem.Rarity.Normal,
                originalDescription = "Simplex Amulet",
            ))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("alch")
        }

        @Test
        fun `magic 1 mod proceed augments`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Magic, mod("A")))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Proceed))
            assertThat(crafter.calls).containsExactly("augment")
        }

        @Test
        fun `magic 1 mod reset alternates`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Magic, mod("A")))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("alternate")
        }

        @Test
        fun `magic 2 mods proceed regals`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Magic, mod("A"), mod("B")))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Proceed))
            assertThat(crafter.calls).containsExactly("regal")
        }

        @Test
        fun `magic 2 mods reset alternates`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Magic, mod("A"), mod("B")))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("alternate")
        }

        @Test
        fun `rare proceed exalts`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Rare, mod("A"), mod("B"), mod("C")))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Proceed))
            assertThat(crafter.calls).containsExactly("exalt")
        }

        @Test
        fun `rare go back annuls`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Rare, mod("A"), mod("B"), mod("C"), mod("D")))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.GoBack))
            assertThat(crafter.calls).containsExactly("annul")
        }

        @Test
        fun `rare reset scours`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Rare, mod("A"), mod("B"), mod("C")))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("scour")
        }

        @Test
        fun `magic 0 mods augments`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Magic))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("augment")
        }

        @Test
        fun `magic heist base regals directly`() = runTest {
            val crafter = RecordingCrafter(item(
                PoeRollableItem.Rarity.Magic,
                originalDescription = "Simplex Amulet",
            ))
            CraftMethods.altAugRegalExaltOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("regal")
        }
    }

    @Nested
    inner class ScourAlchOnce {
        @Test
        fun `normal gets alched`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Normal))
            CraftMethods.scourAlchOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("alch")
        }

        @Test
        fun `magic gets scour then alch`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Magic, mod("A")))
            CraftMethods.scourAlchOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("scour", "alch")
        }

        @Test
        fun `rare gets scour then alch`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Rare, mod("A")))
            CraftMethods.scourAlchOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("scour", "alch")
        }
    }

    @Nested
    inner class ChaosOnce {
        @Test
        fun `rare gets chaos`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Rare, mod("A")))
            CraftMethods.chaosOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("chaos")
        }

        @Test
        fun `normal gets alch`() = runTest {
            val crafter = RecordingCrafter(item(PoeRollableItem.Rarity.Normal))
            CraftMethods.chaosOnce(crafter, fixedDm(DecisionType.Reset))
            assertThat(crafter.calls).containsExactly("alch")
        }
    }
}
