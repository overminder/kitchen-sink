package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.ScreenCommons
import com.gh.om.gamemacros.currentCoroutineScope
import com.gh.om.gamemacros.get
import com.gh.om.gamemacros.isPoeAndTriggerKeyEnabled
import com.gh.om.gamemacros.safeDelay
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.stateIn
import java.awt.Color
import java.awt.Point
import java.time.Duration
import java.time.LocalDateTime

object MouseCap {
    suspend fun printMousePos() {
        val mousePosition = MouseHooks
            .motionEvents()
            .map {
                it.x to it.y
            }
            .stateIn(currentCoroutineScope())

        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!isPoe.value || !pressed) {
                return
            }

            val (x, y) = mousePosition.value
            val color = ScreenCommons.INSTANCE.getPixel(x, y)
            val avgColor = getAverageColor(x, y)
            val avgColorF = getAverageColorFast(x, y)
            val now = LocalDateTime.now()
            println("${now.hour}:${now.minute}:${now.second} Mouse(x = $x, y = $y), color = $color, avgColor = $avgColor, avgColorFast = $avgColorF")
            safeDelay(Duration.ofMillis(1000))
        }
        LEADER_KEY.isEnabled("02").collect(::handle)
    }

    fun getAverageColor(
        x: Int,
        y: Int,
        ranges: Sequence<Point> = genRectRanges(2, 2),
        getter: (Int, Int) -> Color? = ScreenCommons.INSTANCE::getPixel,
    ): Color {
        val colors = ranges.mapNotNull { vec ->
            getter(x + vec.x, y + vec.y)
        }.toList()

        fun averageOf(part: (Color) -> Int) =
            colors.sumOf(part).toDouble() / colors.size
        return Color(
            averageOf(Color::getRed).toInt(),
            averageOf(Color::getGreen).toInt(),
            averageOf(Color::getBlue).toInt(),
        )
    }

    fun getAverageColorFast(
        x: Int,
        y: Int,
        ranges: Sequence<Point> = genRectRanges(30, 30),
    ): Color {
        val getter = ScreenCommons.INSTANCE.captureScreen()
        return getAverageColor(x, y, ranges) { x0, y0 ->
            getter.get(x0, y0)
        }
    }

    fun genRectRanges(
        width: Int,
        height: Int,
    ): Sequence<Point> {
        val halfWidth = width / 2
        val halfHeight = height / 2

        return sequence {
            for (dx in -halfWidth..width) {
                for (dy in -halfHeight..height) {
                    yield(Point(dx, dy))
                }
            }
        }
    }
}
