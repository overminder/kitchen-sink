package com.gh.om.ks.arpgmacro.core

import kotlinx.coroutines.test.runTest
import com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMaker.DecisionType
import com.gh.om.ks.arpgmacro.core.craft.CraftMethods
import com.gh.om.ks.arpgmacro.core.craft.CraftRerollProvider
import com.gh.om.ks.arpgmacro.core.craft.CurrencySlots
import com.gh.om.ks.arpgmacro.core.item.PoeItem
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem
import com.gh.om.ks.arpgmacro.di.GameType
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class CraftRerollProviderTest {
    private lateinit var keyboard: FakeKeyboardOutput
    private lateinit var mouse: FakeMouseOutput
    private lateinit var mouseIn: FakeMouseInput
    private lateinit var clock: FakeClock
    private lateinit var clipboard: FakeClipboard
    private lateinit var screen: FakeScreen
    private lateinit var interactor: PoeInteractor

    private val slots = CurrencySlots(
        transmute = ScreenPoint(1, 1),
        alt = ScreenPoint(2, 2),
        aug = ScreenPoint(3, 3),
        regal = ScreenPoint(4, 4),
        exalt = ScreenPoint(5, 5),
        scour = ScreenPoint(6, 6),
        annul = ScreenPoint(7, 7),
        chaos = ScreenPoint(8, 8),
        alch = ScreenPoint(9, 9),
        armourScrap = ScreenPoint(10, 10),
        whetstone = ScreenPoint(11, 11),
    )

    private val itemSlot = ScreenPoint(100, 100)

    @BeforeEach
    fun setup() {
        keyboard = FakeKeyboardOutput()
        mouse = FakeMouseOutput()
        mouseIn = FakeMouseInput()
        clock = FakeClock()
        clipboard = FakeClipboard()
        screen = FakeScreen()
        interactor = PoeInteractorImpl(keyboard, mouse, mouseIn, clipboard, clock, screen, GameType.POE2)
    }

    private fun mod(
        name: String,
        loc: PoeRollableItem.ExplicitModLocation = PoeRollableItem.ExplicitModLocation.Prefix,
    ) = PoeRollableItem.ExplicitMod(loc = loc, name = name, tier = null, description = "")

    private fun magicItem(vararg mods: PoeRollableItem.ExplicitMod) = PoeRollableItem(
        klass = PoeItem.ConstKlass.Jewels,
        rarity = PoeRollableItem.Rarity.Magic,
        explicitMods = mods.toList(),
        qualities = emptyList(),
        originalDescription = "",
    )

    private fun normalItem() = PoeRollableItem(
        klass = PoeItem.ConstKlass.Jewels,
        rarity = PoeRollableItem.Rarity.Normal,
        explicitMods = emptyList(),
        qualities = emptyList(),
        originalDescription = "",
    )

    /** Decision maker that always returns Reset (to trigger a currency application). */
    private val alwaysReset = _root_ide_package_.com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMaker { _ ->
        _root_ide_package_.com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMaker.Decision(DecisionType.Reset, "test")
    }

    /** Decision maker that always returns Done. */
    private val alwaysDone = _root_ide_package_.com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMaker { _ ->
        _root_ide_package_.com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMaker.Decision(DecisionType.Done, "test")
    }

    @Nested
    inner class FuelTracking {
        @Test
        fun `hasMore returns true when fuel remaining`() = runTest {
            val provider = CraftRerollProvider(
                fuel = 3,
                dm = alwaysReset,
                interactor = interactor,
                currencySlots = slots,
                clock = clock,
            )
            assertThat(provider.hasMore()).isTrue()
        }

        @Test
        fun `fuel decrements on each applyTo`() = runTest {
            val provider = CraftRerollProvider(
                fuel = 2,
                dm = alwaysReset,
                interactor = interactor,
                currencySlots = slots,
                clock = clock,
            )

            assertThat(provider.hasMore()).isTrue()
            provider.applyTo(itemSlot, normalItem())
            assertThat(provider.hasMore()).isTrue()
            provider.applyTo(itemSlot, normalItem())
            assertThat(provider.hasMore()).isFalse()
        }

        @Test
        fun `fuel decrements even when decision is Done`() = runTest {
            val provider = CraftRerollProvider(
                fuel = 1,
                dm = alwaysDone,
                interactor = interactor,
                currencySlots = slots,
                clock = clock,
            )
            provider.applyTo(itemSlot, normalItem())
            assertThat(provider.hasMore()).isFalse()
        }
    }

    @Nested
    inner class CurrencyApplication {
        @Test
        fun `normal item triggers transmute via altAugRegal`() = runTest {
            val provider = CraftRerollProvider(
                fuel = 10,
                dm = alwaysReset,
                interactor = interactor,
                currencySlots = slots,
                clock = clock,
            )
            provider.applyTo(itemSlot, normalItem())

            // altAugRegalExaltOnce on normal -> transmute
            // applyCurrencyTo does: right-click currency, left-click item = 2 clicks
            val clicks = mouse.actions.filterIsInstance<FakeMouseOutput.Action.Click>()
            assertThat(clicks).hasSize(2)
            // First click should be right-click on transmute slot
            assertThat(clicks[0].point).isEqualTo(slots.transmute)
            assertThat(clicks[0].button).isEqualTo(MouseButton.Right)
            // Second click should be left-click on item slot
            assertThat(clicks[1].point).isEqualTo(itemSlot)
            assertThat(clicks[1].button).isEqualTo(MouseButton.Left)
        }

        @Test
        fun `magic 1 mod reset triggers alternate`() = runTest {
            val provider = CraftRerollProvider(
                fuel = 10,
                dm = alwaysReset,
                interactor = interactor,
                currencySlots = slots,
                clock = clock,
            )
            provider.applyTo(itemSlot, magicItem(mod("Bad")))

            val clicks = mouse.actions.filterIsInstance<FakeMouseOutput.Action.Click>()
            assertThat(clicks).hasSize(2)
            assertThat(clicks[0].point).isEqualTo(slots.alt)
        }

        @Test
        fun `custom craft method is used`() = runTest {
            val provider = CraftRerollProvider(
                fuel = 10,
                dm = alwaysReset,
                interactor = interactor,
                currencySlots = slots,
                clock = clock,
                craftMethod = CraftMethods::scourAlchOnce,
            )
            provider.applyTo(itemSlot, normalItem())

            // scourAlchOnce on normal -> alch only
            val clicks = mouse.actions.filterIsInstance<FakeMouseOutput.Action.Click>()
            assertThat(clicks).hasSize(2)
            assertThat(clicks[0].point).isEqualTo(slots.alch)
        }
    }

    @Nested
    inner class ItemCaching {
        @Test
        fun `uses provided item without reading clipboard`() = runTest {
            // Clipboard has nothing — if the provider tries to read,
            // parseAsRollable would get an empty string (Normal with no mods)
            clipboard.content = null

            val provider = CraftRerollProvider(
                fuel = 10,
                dm = alwaysReset,
                interactor = interactor,
                currencySlots = slots,
                clock = clock,
            )

            // Provide a magic item with 1 mod — should trigger alternate
            provider.applyTo(itemSlot, magicItem(mod("Bad")))

            val clicks = mouse.actions.filterIsInstance<FakeMouseOutput.Action.Click>()
            assertThat(clicks[0].point).isEqualTo(slots.alt)
        }
    }
}
