package com.gh.om.ks.arpgmacro.core

/**
 * Screen coordinate constants for POE UI elements at 2560x1440 resolution.
 */
object PoeScreenConstants {
    val firstItemInBag = ScreenPoint(1727, 813)
    val secondItemInBag: ScreenPoint
        get() = ScreenPoint(firstItemInBag.x, firstItemInBag.y + bagGridSize)

    val firstItemInMapStash = ScreenPoint(88, 642)
    val firstItemInHeistLocker = ScreenPoint(550, 554)
    val firstItemInRegularStash = ScreenPoint(57, 201)

    val emptySpaceInRightSideOfBag = ScreenPoint(2429, 688)

    val bagGridSize = 70
    val mapGridSize = 64
    val heistLockerGridSize = 57

    val emptyGridColor = ScreenColor(7, 8, 9)

    val bagRows = 5
    val bagColumns = 10

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
}
