package com.gh.om.ks.arpgmacro.app.impl

import com.github.kwhat.jnativehook.GlobalScreen
import com.github.kwhat.jnativehook.keyboard.NativeKeyEvent
import com.github.kwhat.jnativehook.keyboard.NativeKeyListener
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.callbackFlow
import com.gh.om.ks.arpgmacro.core.KeyboardInput

class JNativeHookKeyboardInput : KeyboardInput {
    override fun keyPresses(): Flow<String> = callbackFlow {
        val listener = object : NativeKeyListener {
            override fun nativeKeyPressed(e: NativeKeyEvent) {
                trySend(NativeKeyEvent.getKeyText(e.keyCode))
            }
        }
        GlobalScreen.addNativeKeyListener(listener)
        awaitClose { GlobalScreen.removeNativeKeyListener(listener) }
    }

    override fun keyReleases(): Flow<String> = callbackFlow {
        val listener = object : NativeKeyListener {
            override fun nativeKeyReleased(e: NativeKeyEvent) {
                trySend(NativeKeyEvent.getKeyText(e.keyCode))
            }
        }
        GlobalScreen.addNativeKeyListener(listener)
        awaitClose { GlobalScreen.removeNativeKeyListener(listener) }
    }
}
