package com.gh.om.ks.arpgmacro.core

import com.gh.om.ks.arpgmacro.core.craft.ChaosRerollProvider
import com.gh.om.ks.arpgmacro.core.craft.ScourAlchRerollProvider
import com.gh.om.ks.arpgmacro.core.item.PoeItem
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem
import kotlinx.coroutines.test.runTest
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class RerollProviderTest {
    private lateinit var keyboard: FakeKeyboardOutput
    private lateinit var mouse: FakeMouseOutput
    private lateinit var clock: FakeClock
    private lateinit var interactor: PoeInteractor

    /**
     * A clipboard that rotates through a list of content strings,
     * one per getText() call.
     */
    private class SequencingClipboard(private val contents: List<String?>) : Clipboard {
        private var index = 0
        override fun getText(): String? {
            if (contents.isEmpty()) return null
            val result = contents[index % contents.size]
            index++
            return result
        }
        override fun setText(text: String) {}
    }

    private val chaosSlot = ScreenPoint(10, 10)
    private val scourSlot = ScreenPoint(20, 20)
    private val alchSlot = ScreenPoint(30, 30)
    private val itemSlot = ScreenPoint(100, 100)

    private val chaosText = """
Item Class: Stackable Currency
Rarity: Currency
Chaos Orb
--------
Stack Size: 50/20
--------
desc
    """.trimIndent()

    private val scourText = """
Item Class: Stackable Currency
Rarity: Currency
Orb of Scouring
--------
Stack Size: 50/20
--------
desc
    """.trimIndent()

    private val alchText = """
Item Class: Stackable Currency
Rarity: Currency
Orb of Alchemy
--------
Stack Size: 50/20
--------
desc
    """.trimIndent()

    @BeforeEach
    fun setup() {
        keyboard = FakeKeyboardOutput()
        mouse = FakeMouseOutput()
        clock = FakeClock()
    }

    private fun makeInteractor(clipboard: Clipboard): PoeInteractor {
        return PoeInteractorImpl(keyboard, mouse, clipboard, clock)
    }

    private fun rareMap() = PoeRollableItem(
        klass = PoeItem.Map(PoeItem.MapTier.T17),
        rarity = PoeRollableItem.Rarity.Rare,
        explicitMods = emptyList(),
        qualities = emptyList(),
        originalDescription = "",
    )

    private fun normalMap() = PoeRollableItem(
        klass = PoeItem.Map(PoeItem.MapTier.Other),
        rarity = PoeRollableItem.Rarity.Normal,
        explicitMods = emptyList(),
        qualities = emptyList(),
        originalDescription = "",
    )

    @Nested
    inner class ScourAlchTests {
        @Test
        fun `hasMore returns true when fuel and currency available`() = runTest {
            // Clipboard returns scour first, then alch
            val clip = SequencingClipboard(listOf(scourText, alchText))
            interactor = makeInteractor(clip)

            val provider = ScourAlchRerollProvider(
                fuel = 100,
                interactor = interactor,
                scourSlot = scourSlot,
                alchSlot = alchSlot,
            )
            assertThat(provider.hasMore()).isTrue()
        }

        @Test
        fun `applyTo scours then alchs a rare item`() = runTest {
            val clip = SequencingClipboard(listOf(scourText, alchText))
            interactor = makeInteractor(clip)

            val provider = ScourAlchRerollProvider(
                fuel = 100,
                interactor = interactor,
                scourSlot = scourSlot,
                alchSlot = alchSlot,
            )
            provider.applyTo(itemSlot, rareMap())

            val clicks = mouse.actions.filterIsInstance<FakeMouseOutput.Action.Click>()
            // scour + alch = 4 clicks (right-click currency + left-click item each)
            assertThat(clicks).hasSize(4)
        }

        @Test
        fun `applyTo only alchs a normal item`() = runTest {
            val clip = SequencingClipboard(listOf(scourText, alchText))
            interactor = makeInteractor(clip)

            val provider = ScourAlchRerollProvider(
                fuel = 100,
                interactor = interactor,
                scourSlot = scourSlot,
                alchSlot = alchSlot,
            )
            provider.applyTo(itemSlot, normalMap())

            val clicks = mouse.actions.filterIsInstance<FakeMouseOutput.Action.Click>()
            // only alch = 2 clicks
            assertThat(clicks).hasSize(2)
        }
    }

    @Nested
    inner class ChaosTests {
        @Test
        fun `applyTo uses chaos on rare items`() = runTest {
            val clip = SequencingClipboard(listOf(chaosText))
            interactor = makeInteractor(clip)

            val provider = ChaosRerollProvider(
                fuel = 100,
                interactor = interactor,
                chaosSlot = chaosSlot,
                scourSlot = scourSlot,
                alchSlot = alchSlot,
            )
            provider.applyTo(itemSlot, rareMap())

            val clicks = mouse.actions.filterIsInstance<FakeMouseOutput.Action.Click>()
            assertThat(clicks).hasSize(2)
        }

        @Test
        fun `fuel limit stops rolling`() = runTest {
            val clip = SequencingClipboard(listOf(chaosText))
            interactor = makeInteractor(clip)

            val provider = ChaosRerollProvider(
                fuel = 2,
                interactor = interactor,
                chaosSlot = chaosSlot,
                scourSlot = scourSlot,
                alchSlot = alchSlot,
            )
            assertThat(provider.hasMore()).isTrue()
            provider.applyTo(itemSlot, rareMap())
            assertThat(provider.hasMore()).isTrue()
            provider.applyTo(itemSlot, rareMap())
            assertThat(provider.hasMore()).isFalse()
        }
    }
}
