package org.example.com.gh.om.gamemacros

import com.github.kwhat.jnativehook.GlobalScreen
import com.github.kwhat.jnativehook.keyboard.NativeKeyEvent
import com.github.kwhat.jnativehook.keyboard.NativeKeyListener
import com.sun.jna.Native
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.time.delay
import java.time.Duration
import java.time.Instant
import java.util.*
import java.util.concurrent.ConcurrentHashMap

fun activeWindows(sampleInterval: Duration = Duration.ofMillis(100)): Flow<String> {
    return activeWindowsThat(sampleInterval) { chars, _ ->
        Native.toString(chars)
    }
}

fun <A> activeWindowsThat(
    sampleInterval: Duration = Duration.ofMillis(100),
    transform: (CharArray, Int) -> A
): Flow<A> {
    return callbackFlow {
        val job = launch {
            val buffer = CharArray(1024)
            while (true) {
                val size = getActiveWindowTitleB(buffer)
                trySend(transform(buffer, size))
                delay(sampleInterval)
            }
        }
        awaitClose {
            job.cancel()
        }
    }.distinctUntilChanged()
}

data class SimpleKeyStates(
    val pressed: Set<String>
)

fun keyStates(): Flow<SimpleKeyStates> {
    val currentState: MutableSet<String> = ConcurrentHashMap.newKeySet<String>()

    fun getKeyText(nativeEvent: NativeKeyEvent): String {
        return NativeKeyEvent.getKeyText(nativeEvent.keyCode)
    }

    return callbackFlow {
        fun sendNewState() {
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

private suspend fun triggerSkillsInD4() {
    val diablo4Title = "Diablo IV".toCharArray()

    fun isDiablo4(
        buffer: CharArray,
        size: Int
    ): Boolean {
        if (size != diablo4Title.size) {
            return false
        }
        return Arrays.equals(buffer, 0, size, diablo4Title, 0, size)
    }

    val isActiveWindowD4 = activeWindowsThat(transform = ::isDiablo4)

    val shouldTrigger = combine(keyStates(), isActiveWindowD4) { keyState, isD4 ->
        "E" in keyState.pressed && isD4
    }.stateIn(CoroutineScope(currentCoroutineContext()))

    var nextIx = 0
    val vcs = listOf(
        NativeKeyEvent.VC_Q,
        NativeKeyEvent.VC_2,
        NativeKeyEvent.VC_3,
        NativeKeyEvent.VC_4,
    )
    val lastTriggers = MutableList<Instant?>(vcs.size) { null }

    fun once() {
        if (!shouldTrigger.value) {
            return
        }

        val now = Instant.now()
        val lastTrigger = lastTriggers[nextIx]
        if (lastTrigger != null && now.isBefore(lastTrigger.plusMillis(100))) {
            // Too soon to trigger. Skip
            return
        }

        lastTriggers[nextIx] = now
        // Do trigger
        postPressRelease(vcs[nextIx])
        nextIx = (nextIx + 1) % vcs.size
    }

    while (true) {
        once()
        delay(Duration.ofMillis(10))
    }
}

private fun postPressRelease(keyCode: Int) {
    val press = NativeKeyEvent(NativeKeyEvent.NATIVE_KEY_PRESSED, 0, 0, keyCode, NativeKeyEvent.CHAR_UNDEFINED)
    val release = NativeKeyEvent(NativeKeyEvent.NATIVE_KEY_RELEASED, 0, 0, keyCode, NativeKeyEvent.CHAR_UNDEFINED)
    GlobalScreen.postNativeEvent(press)
    GlobalScreen.postNativeEvent(release)
}

private fun innerMain() {
    runBlocking {
        triggerSkillsInD4()
    }
}

fun main() {
    GlobalScreen.registerNativeHook()
    try {
        innerMain()
    } finally {
        // NativeHook will create non-daemon thread when key listeners are added.
        // Stop the thread by unregistering the hook.
        GlobalScreen.unregisterNativeHook()
    }
}
