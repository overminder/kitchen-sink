package com.gh.om.gamemacros

import com.github.kwhat.jnativehook.GlobalScreen
import com.github.kwhat.jnativehook.mouse.NativeMouseEvent
import com.github.kwhat.jnativehook.mouse.NativeMouseListener
import com.github.kwhat.jnativehook.mouse.NativeMouseMotionListener
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.callbackFlow
import java.awt.Point
import java.time.Duration

object MouseHooks {
    fun clickEvents(): Flow<NativeMouseEvent> {
        return callbackFlow {
            val motionL = object : NativeMouseListener {
                override fun nativeMouseClicked(nativeEvent: NativeMouseEvent) {
                    trySend(nativeEvent)
                }
            }
            GlobalScreen.addNativeMouseListener(motionL)
            awaitClose {
                GlobalScreen.removeNativeMouseListener(motionL)
            }
        }
    }

    fun motionEvents(): Flow<NativeMouseEvent> {
        return callbackFlow {
            val motionL = object : NativeMouseMotionListener {
                override fun nativeMouseMoved(nativeEvent: NativeMouseEvent) {
                    trySend(nativeEvent)
                }

                override fun nativeMouseDragged(nativeEvent: NativeMouseEvent) {
                    trySend(nativeEvent)
                }
            }
            GlobalScreen.addNativeMouseMotionListener(motionL)
            awaitClose {
                GlobalScreen.removeNativeMouseMotionListener(motionL)
            }
        }
    }

    fun moveTo(
        point: Point,
    ) {
        moveTo(point.x, point.y)
    }

    fun moveTo(
        x: Int,
        y: Int
    ) {
        val ev = NativeMouseEvent(
            NativeMouseEvent.NATIVE_MOUSE_MOVED,
            0,
            x,
            y,
            1,
            NativeMouseEvent.NOBUTTON
        )
        GlobalScreen.postNativeEvent(ev)
    }

    suspend fun postClick(
        point: Point,
        button: Int = NativeMouseEvent.BUTTON1,
        delayMs: Long = 50,
        moveFirst: Boolean = false,
    ) {
        postClick(
            x = point.x,
            y = point.y,
            button = button,
            delayMs = delayMs,
            moveFirst = moveFirst
        )
    }

    suspend fun postClick(
        x: Int,
        y: Int,
        button: Int = NativeMouseEvent.BUTTON1,
        delayMs: Long = 16,
        moveFirst: Boolean = false,
    ) {
        val ev = NativeMouseEvent(
            NativeMouseEvent.NATIVE_MOUSE_PRESSED,
            0,
            x,
            y,
            1,
            button
        )
        val ev2 = NativeMouseEvent(
            NativeMouseEvent.NATIVE_MOUSE_RELEASED,
            0,
            x,
            y,
            1,
            button
        )
        if (moveFirst) {
            moveTo(x, y)
            safeDelay(Duration.ofMillis(delayMs))
        }
        GlobalScreen.postNativeEvent(ev)
        safeDelay(Duration.ofMillis(delayMs))
        GlobalScreen.postNativeEvent(ev2)
    }
}
