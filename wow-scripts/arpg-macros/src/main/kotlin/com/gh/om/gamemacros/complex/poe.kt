package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.currentCoroutineScope
import com.gh.om.gamemacros.isPoeAndTriggerKeyEnabled
import com.gh.om.gamemacros.safeDelay
import com.github.kwhat.jnativehook.mouse.NativeMouseEvent
import kotlinx.coroutines.flow.stateIn
import java.awt.Point

object PoeStackedDeck {
    val firstItemInBag = Point(1727, 813)
    val ground = Point(1628, 813)

    suspend fun unstackEntireStack() {
        val isPoe = isPoeAndTriggerKeyEnabled(
            setOf("F4")
        )
        val mouseEvents =
            MouseHooks.motionEvents().stateIn(currentCoroutineScope())

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            // So we can start from any slot in bag
            val initial = mouseEvents.value.point
            repeat(20) {
                if (!isPoe.value) {
                    return
                }
                unstackOnce(initial = initial)
            }
        }
        LEADER_KEY.isEnabled("03").collect(::handle)
    }

    private suspend fun unstackOnce(initial: Point = firstItemInBag) {
        // Right click deck
        MouseHooks.postClick(
            x = initial.x,
            y = initial.y,
            button = NativeMouseEvent.BUTTON2,
            delayMs = 50,
            moveFirst = true,
        )
        safeDelay()
        MouseHooks.postClick(
            x = ground.x,
            y = ground.y,
            button = NativeMouseEvent.BUTTON1,
            delayMs = 50,
            moveFirst = true,
        )
        safeDelay()
    }
}
