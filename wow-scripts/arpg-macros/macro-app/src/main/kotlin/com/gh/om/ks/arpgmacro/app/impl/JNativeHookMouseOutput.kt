package com.gh.om.ks.arpgmacro.app.impl

import com.github.kwhat.jnativehook.GlobalScreen
import com.github.kwhat.jnativehook.mouse.NativeMouseEvent
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.MouseButton
import com.gh.om.ks.arpgmacro.core.MouseOutput
import com.gh.om.ks.arpgmacro.core.ScreenPoint
import kotlin.time.Duration.Companion.milliseconds

class JNativeHookMouseOutput(
    private val clock: Clock,
) : MouseOutput {

    override fun moveTo(point: ScreenPoint) {
        val event = NativeMouseEvent(
            NativeMouseEvent.NATIVE_MOUSE_MOVED,
            0, point.x, point.y, 1, NativeMouseEvent.NOBUTTON,
        )
        GlobalScreen.postNativeEvent(event)
    }

    override suspend fun postClick(
        point: ScreenPoint,
        button: MouseButton,
        delayMs: Long,
        moveFirst: Boolean,
    ) {
        val nativeButton = when (button) {
            MouseButton.Left -> NativeMouseEvent.BUTTON1
            MouseButton.Right -> NativeMouseEvent.BUTTON2
        }

        if (moveFirst) {
            moveTo(point)
            clock.delay(delayMs.milliseconds)
        }

        val press = NativeMouseEvent(
            NativeMouseEvent.NATIVE_MOUSE_PRESSED,
            0, point.x, point.y, 1, nativeButton,
        )
        GlobalScreen.postNativeEvent(press)

        clock.delay(delayMs.milliseconds)

        val release = NativeMouseEvent(
            NativeMouseEvent.NATIVE_MOUSE_RELEASED,
            0, point.x, point.y, 1, nativeButton,
        )
        GlobalScreen.postNativeEvent(release)
    }
}
