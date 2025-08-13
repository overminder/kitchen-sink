package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.currentCoroutineScope
import com.gh.om.gamemacros.isPoeAndTriggerKeyEnabled
import com.gh.om.gamemacros.safeDelay
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.stateIn
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

        val isPoe = isPoeAndTriggerKeyEnabled(
            setOf("F4")
        )

        suspend fun handle(pressed: Boolean) {
            if (!isPoe.value || !pressed) {
                return
            }

            val (x, y) = mousePosition.value
            val now = LocalDateTime.now()
            println("${now.hour}:${now.minute}:${now.second} Mouse(x = $x, y = $y)")
            safeDelay(Duration.ofMillis(1000))
        }
        LEADER_KEY.isEnabled("02").collect(::handle)
    }
}
