package com.gh.om.ks.arpgmacro.core

import com.gh.om.ks.arpgmacro.di.GameType
import java.awt.Color
import java.awt.Point

/**
 * Screen coordinate constants for POE UI elements at 2560x1440 resolution.
 */
object PoeScreenConstants {
    val firstItemInBag = ScreenPoint(1727, 813)
    // y = 824, not too off
    private val firstItemInBagPoe2 = firstItemInBag.offset(dy = 11)

    val firstItemInMapStash = ScreenPoint(88, 642)
    val firstItemInHeistLocker = ScreenPoint(550, 554)
    val firstItemInRegularStash = ScreenPoint(57, 201)

    val emptySpaceInRightSideOfBag = ScreenPoint(2429, 688)

    // This is also the same for POE2
    val bagGridSize = 70
    val mapGridSize = 64
    val heistLockerGridSize = 57
    val halfSmallestGridSize = listOf(
        bagGridSize, mapGridSize, heistLockerGridSize
    ).min() / 2

    val emptyGridColor = ScreenColor(7, 8, 9)

    val bagRows = 5
    val bagColumns = 10

    fun firstItemInBagFor(gameType: GameType): ScreenPoint {
        return when (gameType) {
            GameType.POE1 -> firstItemInBag
            GameType.POE2 -> firstItemInBagPoe2
            GameType.Diablo3,
            GameType.Diablo4 -> TODO("Do we need a bag macro for $gameType?")
        }
    }

    /**
     * Generate all grid slot positions given a starting point and grid dimensions.
     * Iterates columns first, then rows within each column.
     */
    fun allGrids(
        start: ScreenPoint,
        rows: Int,
        columns: Int,
        gridSize: Int,
    ): Sequence<ScreenPoint> = sequence {
        for (x in 0 until columns) {
            for (y in 0 until rows) {
                yield(
                    ScreenPoint(
                        start.x + x * gridSize,
                        start.y + y * gridSize,
                    )
                )
            }
        }
    }

    /**
     * Check if a grid cell color indicates an item is present
     * (i.e., it doesn't match the empty grid background color).
     */
    fun gridColorHasItem(color: ScreenColor, maxDistance: Int = 7): Boolean {
        return color.distanceTo(emptyGridColor) >= maxDistance
    }

    /**
     * Filter grid positions to only those containing items,
     * using a captured pixel source.
     */
    fun filterOccupiedSlots(
        slots: Sequence<ScreenPoint>,
        pixelSource: PixelSource,
        maxDistance: Int = 7,
    ): List<ScreenPoint> {
        return slots.filter { slot ->
            gridColorHasItem(pixelSource.getPixelColor(slot), maxDistance)
        }.toList()
    }

    /**
     * Uses [getAverageColor] for better reliability.
     */
    fun filterOccupiedSlotsV2(
        slots: List<ScreenPoint>,
        pixelSource: PixelSource,
        maxDistance: Int = 7,
    ): List<IndexedValue<ScreenPoint>> {
        return slots.mapIndexedNotNull { index, slot ->
            val color = getAverageColor(
                slot.offset(-halfSmallestGridSize, -halfSmallestGridSize),
                slot.offset(halfSmallestGridSize, halfSmallestGridSize),
                pixelSource,
            )
            if (gridColorHasItem(color, maxDistance)) {
                IndexedValue(index, slot)
            } else {
                null
            }
        }.toList()
    }
}

private fun getAverageColor(
    leftTop: ScreenPoint,
    bottomRight: ScreenPoint,
    pixelSource: PixelSource,
): ScreenColor {
    val colors = mutableListOf<ScreenColor>()
    for (y in leftTop.y .. bottomRight.y) {
        for (x in leftTop.x .. bottomRight.x) {
            colors += pixelSource.getPixelColor(ScreenPoint(x, y))
        }
    }

    fun averageOf(part: (ScreenColor) -> Int) =
        colors.sumOf(part).toDouble() / colors.size
    return ScreenColor(
        averageOf(ScreenColor::r).toInt(),
        averageOf(ScreenColor::g).toInt(),
        averageOf(ScreenColor::b).toInt(),
    )
}
