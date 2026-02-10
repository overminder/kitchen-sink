package com.gh.om.ks.arpgmacro.app.impl

import com.github.kwhat.jnativehook.GlobalScreen
import com.github.kwhat.jnativehook.mouse.NativeMouseEvent
import com.github.kwhat.jnativehook.mouse.NativeMouseListener
import com.github.kwhat.jnativehook.mouse.NativeMouseMotionListener
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.callbackFlow
import com.gh.om.ks.arpgmacro.core.MouseInput
import com.gh.om.ks.arpgmacro.core.ScreenPoint

class JNativeHookMouseInput : MouseInput {
    override fun clickEvents(): Flow<ScreenPoint> = callbackFlow {
        val listener = object : NativeMouseListener {
            override fun nativeMouseClicked(e: NativeMouseEvent) {
                trySend(ScreenPoint(e.point.x, e.point.y))
            }
        }
        GlobalScreen.addNativeMouseListener(listener)
        awaitClose { GlobalScreen.removeNativeMouseListener(listener) }
    }

    override fun motionEvents(): Flow<ScreenPoint> = callbackFlow {
        val listener = object : NativeMouseMotionListener {
            override fun nativeMouseMoved(e: NativeMouseEvent) {
                trySend(ScreenPoint(e.point.x, e.point.y))
            }
        }
        GlobalScreen.addNativeMouseMotionListener(listener)
        awaitClose { GlobalScreen.removeNativeMouseMotionListener(listener) }
    }
}
