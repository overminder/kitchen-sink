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
        getter: (Int, Int) -> Color? = ScreenCommons.INSTANCE::getPixel,
    ): Color {
        val colors = mutableListOf<Color>()
        for (dx in -1..1) {
            for (dy in -1..1) {
                getter(x + dx * 2, y + dy * 2)?.let(colors::add)
            }
        }
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
    ): Color {
        val getter = ScreenCommons.INSTANCE.captureScreen()
        return getAverageColor(x, y) { x0, y0 ->
            getter.get(x0, y0)
        }
    }
}
