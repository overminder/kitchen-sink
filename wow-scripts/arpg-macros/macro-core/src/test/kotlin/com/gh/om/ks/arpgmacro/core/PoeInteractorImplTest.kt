package com.gh.om.ks.arpgmacro.core

import com.gh.om.ks.arpgmacro.core.item.PoeCurrency
import kotlinx.coroutines.test.runTest
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class PoeInteractorImplTest {
    private lateinit var keyboard: FakeKeyboardOutput
    private lateinit var mouse: FakeMouseOutput
    private lateinit var clipboard: FakeClipboard
    private lateinit var clock: FakeClock
    private lateinit var interactor: PoeInteractorImpl

    @BeforeEach
    fun setup() {
        keyboard = FakeKeyboardOutput()
        mouse = FakeMouseOutput()
        clipboard = FakeClipboard()
        clock = FakeClock()
        interactor = PoeInteractorImpl(keyboard, mouse, clipboard, clock)
    }

    @Nested
    inner class GetItemDescription {
        @Test
        fun `moves mouse and copies with Ctrl+Alt+C`() = runTest {
            clipboard.content = "Item Class: Maps\nRarity: Rare\nTest Map"

            val result = interactor.getItemDescriptionAt(ScreenPoint(100, 200))

            assertThat(result).isEqualTo("Item Class: Maps\nRarity: Rare\nTest Map")

            // Verify mouse was moved
            assertThat(mouse.actions).isNotEmpty()
            assertThat(mouse.actions[0]).isEqualTo(
                FakeMouseOutput.Action.MoveTo(ScreenPoint(100, 200))
            )

            // Verify modifier keys were used
            val pressKeys = keyboard.events.filter { it.pressed }.map { it.keyCode }
            assertThat(pressKeys).contains("Ctrl", "Alt", "C")
        }

        @Test
        fun `returns null when clipboard is empty`() = runTest {
            clipboard.content = null
            val result = interactor.getItemDescriptionAt(ScreenPoint(100, 200))
            assertThat(result).isNull()
        }
    }

    @Nested
    inner class ApplyCurrencyTo {
        @Test
        fun `right-clicks currency then left-clicks item`() = runTest {
            val currencySlot = ScreenPoint(50, 50)
            val itemSlot = ScreenPoint(200, 200)

            interactor.applyCurrencyTo(currencySlot, itemSlot)

            val clicks = mouse.actions.filterIsInstance<FakeMouseOutput.Action.Click>()
            assertThat(clicks).hasSize(2)
            assertThat(clicks[0].point).isEqualTo(currencySlot)
            assertThat(clicks[0].button).isEqualTo(MouseButton.Right)
            assertThat(clicks[0].moveFirst).isTrue()
            assertThat(clicks[1].point).isEqualTo(itemSlot)
            assertThat(clicks[1].button).isEqualTo(MouseButton.Left)
            assertThat(clicks[1].moveFirst).isTrue()
        }
    }

    @Nested
    inner class CtrlClick {
        @Test
        fun `presses ctrl before click and releases after`() = runTest {
            val point = ScreenPoint(100, 100)
            interactor.sendItemToOtherSide(point)

            // Ctrl should be pressed and released
            val ctrlPress = keyboard.events.indexOfFirst { it.keyCode == "Ctrl" && it.pressed }
            val ctrlRelease = keyboard.events.indexOfFirst { it.keyCode == "Ctrl" && !it.pressed }
            assertThat(ctrlPress).isGreaterThanOrEqualTo(0)
            assertThat(ctrlRelease).isGreaterThan(ctrlPress)

            // Click should happen
            val clicks = mouse.actions.filterIsInstance<FakeMouseOutput.Action.Click>()
            assertThat(clicks).hasSize(1)
            assertThat(clicks[0].point).isEqualTo(point)
        }
    }

    @Nested
    inner class CtrlShiftClick {
        @Test
        fun `presses ctrl and shift before click`() = runTest {
            val point = ScreenPoint(100, 100)
            interactor.forceSendItemToCurrentStash(point)

            val pressKeys = keyboard.events.filter { it.pressed }.map { it.keyCode }
            assertThat(pressKeys).contains("Ctrl", "Shift")

            val clicks = mouse.actions.filterIsInstance<FakeMouseOutput.Action.Click>()
            assertThat(clicks).hasSize(1)
        }
    }

    @Nested
    inner class GetCurrencyCount {
        @Test
        fun `reads currency count from clipboard`() = runTest {
            clipboard.content = """
Item Class: Stackable Currency
Rarity: Currency
Chaos Orb
--------
Stack Size: 47/20
--------
Reforges a rare item with new random modifiers
            """.trimIndent()

            val count = interactor.getCurrencyCountAt(
                ScreenPoint(50, 50),
                listOf(PoeCurrency.Chaos),
            )
            assertThat(count).isEqualTo(47)
        }

        @Test
        fun `returns 0 for wrong currency type`() = runTest {
            clipboard.content = """
Item Class: Stackable Currency
Rarity: Currency
Orb of Scouring
--------
Stack Size: 30/20
--------
Removes all properties from an item
            """.trimIndent()

            val count = interactor.getCurrencyCountAt(
                ScreenPoint(50, 50),
                listOf(PoeCurrency.Chaos),
            )
            assertThat(count).isEqualTo(0)
        }

        @Test
        fun `returns 0 when clipboard is empty`() = runTest {
            clipboard.content = null
            val count = interactor.getCurrencyCountAt(
                ScreenPoint(50, 50),
                listOf(PoeCurrency.Chaos),
            )
            assertThat(count).isEqualTo(0)
        }
    }
}
