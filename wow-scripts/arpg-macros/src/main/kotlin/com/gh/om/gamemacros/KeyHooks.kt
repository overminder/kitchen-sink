package com.gh.om.gamemacros

import com.github.kwhat.jnativehook.GlobalScreen
import com.github.kwhat.jnativehook.keyboard.NativeKeyEvent
import com.github.kwhat.jnativehook.keyboard.NativeKeyListener
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.callbackFlow
import kotlinx.coroutines.flow.distinctUntilChanged
import java.util.concurrent.ConcurrentHashMap

data class SimpleKeyStates(
    val pressed: Set<String>
)

object KeyHooks {
    fun keyReleases(): Flow<String> {
        return callbackFlow {
            val kl = object : NativeKeyListener {
                override fun nativeKeyReleased(nativeEvent: NativeKeyEvent) {
                    // XXX what to do if channel is full?
                    trySend(getKeyText(nativeEvent))
                }
            }
            GlobalScreen.addNativeKeyListener(kl)
            awaitClose {
                GlobalScreen.removeNativeKeyListener(kl)
            }
        }.distinctUntilChanged()
    }

    fun keyStates(): Flow<SimpleKeyStates> {
        val currentState: MutableSet<String> = ConcurrentHashMap.newKeySet<String>()

        return callbackFlow {
            fun sendNewState() {
                // Re trySend: It's fine to sometimes drop key state changes,
                // since it represents the full state rather than an
                // incremental update.
                trySend(SimpleKeyStates(currentState.toSet()))
            }

            val kl = object : NativeKeyListener {
                override fun nativeKeyPressed(nativeEvent: NativeKeyEvent) {
                    currentState += getKeyText(nativeEvent)
                    sendNewState()
                }

                override fun nativeKeyReleased(nativeEvent: NativeKeyEvent) {
                    currentState -= getKeyText(nativeEvent)
                    sendNewState()
                }
            }
            GlobalScreen.addNativeKeyListener(kl)
            awaitClose {
                GlobalScreen.removeNativeKeyListener(kl)
            }
        }.distinctUntilChanged()
    }

    fun postPressRelease(keyCode: Int) {
        val press = NativeKeyEvent(NativeKeyEvent.NATIVE_KEY_PRESSED, 0, 0, keyCode, NativeKeyEvent.CHAR_UNDEFINED)
        val release = NativeKeyEvent(NativeKeyEvent.NATIVE_KEY_RELEASED, 0, 0, keyCode, NativeKeyEvent.CHAR_UNDEFINED)
        GlobalScreen.postNativeEvent(press)
        GlobalScreen.postNativeEvent(release)
    }

    fun postAsciiString(string: String) {
        for (c in string) {
            postPressRelease(getKeyCodeFromAsciiChar(c))
        }
    }
}

private fun getKeyCodeFromAsciiChar(c: Char): Int {
    SPECIAL_CASE_KEY_CODES[c]?.let {
        return it
    }

    val klass = NativeKeyEvent::class.java
    val f = klass.getField("VC_${c.uppercaseChar()}")
    return f.get(null) as Int
}

private val SPECIAL_CASE_KEY_CODES = mapOf(
    '/' to NativeKeyEvent.VC_SLASH,
)

private fun getKeyText(nativeEvent: NativeKeyEvent): String {
    return NativeKeyEvent.getKeyText(nativeEvent.keyCode)
}
