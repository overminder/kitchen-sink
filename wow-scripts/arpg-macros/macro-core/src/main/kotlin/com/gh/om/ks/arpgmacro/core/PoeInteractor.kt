package com.gh.om.ks.arpgmacro.core

import com.gh.om.ks.arpgmacro.core.item.PoeCurrency
import com.gh.om.ks.arpgmacro.core.item.PoeItem
import com.gh.om.ks.arpgmacro.core.item.PoeItemParser
import com.gh.om.ks.arpgmacro.di.GameType
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.firstOrNull
import javax.inject.Inject
import kotlin.time.Duration.Companion.milliseconds

/**
 * High-level POE game interaction primitives built on platform abstractions.
 * Composes raw keyboard/mouse/clipboard actions into game-specific operations.
 */
interface PoeInteractor {
    /**
     * Advanced description by default.
     */
    suspend fun getItemDescriptionAt(point: ScreenPoint): String?
    suspend fun applyCurrencyTo(currencySlot: ScreenPoint, itemSlot: ScreenPoint)

    /**
     * Basically ctrl-click.
     * bag -> stash (respecting stash affinity), or stash to bag.
     */
    suspend fun sendItemToOtherSide(point: ScreenPoint)
    suspend fun forceSendItemToCurrentStash(point: ScreenPoint)
    suspend fun getCurrencyCountAt(point: ScreenPoint, types: List<PoeCurrency.KnownType>): Int
    suspend fun getOccupiedBagSlots(
        rows: Int = PoeScreenConstants.bagRows,
        columns: Int = PoeScreenConstants.bagColumns,
        includeEmptySlotAfter: Boolean = false,
    ): List<ScreenPoint>
}

class PoeInteractorImpl @Inject constructor(
    private val keyboard: KeyboardOutput,
    private val mouseOut: MouseOutput,
    private val mouseIn: MouseInput,
    private val clipboard: Clipboard,
    private val clock: Clock,
    private val screen: Screen,
    private val gameType: GameType,
) : PoeInteractor {
    /**
     * Move mouse to [point], press Ctrl+Alt+C to copy advanced description,
     * wait, and return clipboard text.
     */
    override suspend fun getItemDescriptionAt(point: ScreenPoint): String? {
        clock.delay(30.milliseconds)
        mouseOut.moveTo(point)
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

    override suspend fun getOccupiedBagSlots(
        rows: Int,
        columns: Int,
        includeEmptySlotAfter: Boolean,
    ): List<ScreenPoint> {
        val screenCap = withMouseAwayFromBag {
            screen.captureScreen()
        }
        val allGrids = PoeScreenConstants.allGrids(
            start = PoeScreenConstants.firstItemInBagFor(gameType),
            rows = rows,
            columns = columns,
            gridSize = PoeScreenConstants.bagGridSize,
        ).toList()
        val indexedSlots = PoeScreenConstants.filterOccupiedSlotsV2(
            allGrids,
            screenCap
        )
        val occupied = indexedSlots.map { it.value }
        return if (includeEmptySlotAfter) {
            val oneBeyondLastSlotIndex = indexedSlots.lastOrNull()?.index?.let { it + 1 } ?: 0
            val emptySlot = allGrids[oneBeyondLastSlotIndex]
            occupied + emptySlot
        } else {
            occupied
        }
    }

    /**
     * Apply currency at [currencySlot] to item at [itemSlot].
     * Right-clicks currency, then left-clicks item.
     */
    override suspend fun applyCurrencyTo(currencySlot: ScreenPoint, itemSlot: ScreenPoint) {
        mouseOut.postClick(
            point = currencySlot,
            button = MouseButton.Right,
            moveFirst = true,
        )
        clock.delay(30.milliseconds)
        mouseOut.postClick(
            point = itemSlot,
            button = MouseButton.Left,
            moveFirst = true,
        )
        clock.delay(30.milliseconds)
    }

    /**
     * Ctrl+click an item (quick-move).
     */
    override suspend fun sendItemToOtherSide(point: ScreenPoint) {
        withModifier("Ctrl") {
            mouseOut.postClick(point, moveFirst = true)
            clock.delay(30.milliseconds)
        }
    }

    /**
     * Ctrl+Shift+click an item (quick-move to specific tab).
     */
    override suspend fun forceSendItemToCurrentStash(point: ScreenPoint) {
        withModifier("Ctrl") {
            withModifier("Shift") {
                mouseOut.postClick(point, moveFirst = true)
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
        mouseOut.moveTo(point)
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

    /**
     * Useful for screen cap to avoid mouse cursor being captured in the bag area.
     */
    private suspend fun <A> withMouseAwayFromBag(action: () -> A): A {
        // XXX can't simply get mouse's current position from mouseIn flow -- that
        // flow only emits after mouse moves.
        clock.delay(100.milliseconds)
        mouseOut.moveTo(PoeScreenConstants.emptySpaceInRightSideOfBag)
        clock.delay(100.milliseconds)
        val result = action()
        clock.delay(100.milliseconds)
        return result
    }
}

suspend fun PoeInteractor.parseItemAt(point: ScreenPoint): PoeItem? {
    val ad = getItemDescriptionAt(point).orEmpty()
    return PoeItemParser.parse(ad)
}
