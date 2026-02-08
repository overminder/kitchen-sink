package com.gh.om.ks.arpgmacro.core

import javax.inject.Inject
import kotlin.time.Duration.Companion.milliseconds

/**
 * High-level POE game interaction primitives built on platform abstractions.
 * Composes raw keyboard/mouse/clipboard actions into game-specific operations.
 */
interface PoeInteractor {
    suspend fun getItemDescriptionAt(point: ScreenPoint): String?
    suspend fun applyCurrencyTo(currencySlot: ScreenPoint, itemSlot: ScreenPoint)
    suspend fun ctrlClick(point: ScreenPoint)
    suspend fun ctrlShiftClick(point: ScreenPoint)
    suspend fun getCurrencyCountAt(point: ScreenPoint, types: List<PoeCurrency.KnownType>): Int
}

class PoeInteractorImpl @Inject constructor(
    private val keyboard: KeyboardOutput,
    private val mouse: MouseOutput,
    private val clipboard: Clipboard,
    private val clock: Clock,
) : PoeInteractor {
    /**
     * Move mouse to [point], press Ctrl+Alt+C to copy advanced description,
     * wait, and return clipboard text.
     */
    override suspend fun getItemDescriptionAt(point: ScreenPoint): String? {
        mouse.moveTo(point)
        clock.delay(30.milliseconds)

        withModifier("Ctrl") {
            withModifier("Alt") {
                keyboard.postPress("C")
                clock.delay(30.milliseconds)
                keyboard.postRelease("C")
                clock.delay(30.milliseconds)
            }
        }
        clock.delay(100.milliseconds)
        return clipboard.getText()
    }

    /**
     * Apply currency at [currencySlot] to item at [itemSlot].
     * Right-clicks currency, then left-clicks item.
     */
    override suspend fun applyCurrencyTo(currencySlot: ScreenPoint, itemSlot: ScreenPoint) {
        mouse.postClick(
            point = currencySlot,
            button = MouseButton.Right,
            moveFirst = true,
        )
        clock.delay(30.milliseconds)
        mouse.postClick(
            point = itemSlot,
            button = MouseButton.Left,
            moveFirst = true,
        )
        clock.delay(30.milliseconds)
    }

    /**
     * Ctrl+click an item (quick-move).
     */
    override suspend fun ctrlClick(point: ScreenPoint) {
        withModifier("Ctrl") {
            mouse.postClick(point, moveFirst = true)
            clock.delay(30.milliseconds)
        }
    }

    /**
     * Ctrl+Shift+click an item (quick-move to specific tab).
     */
    override suspend fun ctrlShiftClick(point: ScreenPoint) {
        withModifier("Ctrl") {
            withModifier("Shift") {
                mouse.postClick(point, moveFirst = true)
                clock.delay(30.milliseconds)
            }
        }
    }

    /**
     * Read the stack count of a currency item at [point], verifying it matches
     * one of the expected [types].
     */
    override suspend fun getCurrencyCountAt(
        point: ScreenPoint,
        types: List<PoeCurrency.KnownType>,
    ): Int {
        mouse.moveTo(point)
        clock.delay(30.milliseconds)

        // Use simple Ctrl+C (not advanced description) for currency
        withModifier("Ctrl") {
            keyboard.postPress("C")
            clock.delay(30.milliseconds)
            keyboard.postRelease("C")
            clock.delay(30.milliseconds)
        }
        clock.delay(100.milliseconds)

        val text = clipboard.getText() ?: return 0
        val item = PoeItemParser.parse(text) as? PoeCurrency ?: return 0
        return if (item.type in types) item.stackSize else 0
    }

    private suspend fun withModifier(key: String, block: suspend () -> Unit) {
        keyboard.postPress(key)
        clock.delay(30.milliseconds)
        try {
            block()
        } finally {
            keyboard.postRelease(key)
            clock.delay(30.milliseconds)
        }
    }
}
