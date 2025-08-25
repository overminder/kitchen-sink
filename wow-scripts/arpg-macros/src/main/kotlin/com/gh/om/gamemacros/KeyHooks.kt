package com.gh.om.gamemacros

import com.github.kwhat.jnativehook.GlobalScreen
import com.github.kwhat.jnativehook.keyboard.NativeKeyEvent
import com.github.kwhat.jnativehook.keyboard.NativeKeyListener
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.callbackFlow
import kotlinx.coroutines.flow.distinctUntilChanged
import kotlinx.coroutines.flow.map
import java.time.Duration
import java.util.concurrent.ConcurrentHashMap
import kotlin.time.Duration.Companion.milliseconds

data class SimpleKeyStates(
    val pressed: Set<String>,
)

object KeyHooks {
    fun keyPresses(): Flow<String> {
        return callbackFlow {
            val kl = object : NativeKeyListener {
                override fun nativeKeyPressed(nativeEvent: NativeKeyEvent) {
                    trySend(getKeyText(nativeEvent))
                }
            }
            GlobalScreen.addNativeKeyListener(kl)
            awaitClose {
                GlobalScreen.removeNativeKeyListener(kl)
            }
        }
    }

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
        }
    }

    fun keyStates(): Flow<SimpleKeyStates> {
        val currentState: MutableSet<String> =
            ConcurrentHashMap.newKeySet<String>()

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

    suspend fun withModifierKey(
        keyCode: Int,
        inner: suspend () -> Unit,
    ) {
        postPress(keyCode)
        safeDelayK(30.milliseconds)
        try {
            inner()
        } finally {
            postRelease(keyCode)
            // Important to also delay here (otherwise nested call means
            // multiple releases are done at the same time, breaking poe's
            // key handling)
            safeDelayK(30.milliseconds)
        }
    }

    fun postPress(keyCode: Int) {
        val press = NativeKeyEvent(
            NativeKeyEvent.NATIVE_KEY_PRESSED,
            0,
            0,
            keyCode,
            NativeKeyEvent.CHAR_UNDEFINED
        )
        GlobalScreen.postNativeEvent(press)
    }

    fun postRelease(keyCode: Int) {
        val release = NativeKeyEvent(
            NativeKeyEvent.NATIVE_KEY_RELEASED,
            0,
            0,
            keyCode,
            NativeKeyEvent.CHAR_UNDEFINED
        )
        GlobalScreen.postNativeEvent(release)
    }

    fun postPressRelease(keyCode: Int) {
        postPress(keyCode)
        postRelease(keyCode)
    }

    suspend fun postPressWaitRelease(
        keyCodes: List<Int>,
        waitTime: Duration,
    ) {
        try {
            keyCodes.forEach(::postPress)
            safeDelay(waitTime)
        } finally {
            keyCodes.forEach(::postRelease)
        }
    }

    fun postAsciiString(string: String) {
        for (c in string) {
            postPressRelease(getKeyCodeFromAsciiChar(c))
        }
    }
}

object KeyHooksEx {
    fun keyPressed(
        key: String,
        sampleInterval: Duration? = Duration.ofMillis(100),
    ): Flow<Boolean> {
        val presses = KeyHooks
            .keyStates()
            .map { key in it.pressed }
            // | Important! Otherwise keyStates are constantly changing
            .distinctUntilChanged()
        return if (sampleInterval != null) {
            presses.sampleAndReemit(sampleInterval)
        } else {
            presses
        }
    }

    enum class Conj {
        And,
        Or,
    }

    fun keysPressed(
        keys: List<String>,
        conj: Conj = Conj.And,
        sampleInterval: Duration? = Duration.ofMillis(100),
    ): Flow<Boolean> {
        var previousState: Set<String> = emptySet()
        val presses = KeyHooks
            .keyStates()
            .map {
                val keySet = it.pressed
                if (previousState != keySet) {
                    // Debug (can't replicate hmm)
                    // println("keyStates change: $previousState -> $keySet")
                    previousState = keySet
                }
                val check = when (conj) {
                    Conj.And -> keys::all
                    Conj.Or -> keys::any
                }
                check { key -> key in it.pressed }
            }
            // | Important! Otherwise keyStates are constantly changing
            .distinctUntilChanged()
        return if (sampleInterval != null) {
            presses.sampleAndReemit(sampleInterval)
        } else {
            presses
        }
    }
}

fun getKeyCodeFromAsciiChar(c: Char): Int {
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
