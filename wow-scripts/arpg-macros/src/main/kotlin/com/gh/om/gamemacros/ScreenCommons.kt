package com.gh.om.gamemacros

import com.sun.jna.Native
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.callbackFlow
import kotlinx.coroutines.flow.distinctUntilChanged
import kotlinx.coroutines.launch
import kotlinx.coroutines.time.delay
import org.example.com.gh.om.gamemacros.Win32Api
import java.time.Duration
import java.util.*

// TODO: This is not cross platform yet. Make it work on Mac
object ScreenCommons {
    fun activeWindows(
        sampleInterval: Duration = Duration.ofMillis(100)
    ): Flow<String> {
        return activeWindowsThat(sampleInterval) { chars, _ ->
            Native.toString(chars)
        }
    }

    fun activeWindowHas(
        title: String,
        sampleInterval: Duration = Duration.ofMillis(100),
    ): Flow<Boolean> {
        val titleChars = title.toCharArray()

        fun check(
            buffer: CharArray,
            size: Int
        ): Boolean {
            if (size != titleChars.size) {
                return false
            }
            return Arrays.equals(buffer, 0, size, titleChars, 0, size)
        }

        return activeWindowsThat(sampleInterval, transform = ::check)
    }

    fun <A> activeWindowsThat(
        sampleInterval: Duration = Duration.ofMillis(100),
        transform: (CharArray, Int) -> A
    ): Flow<A> {
        return callbackFlow {
            val job = launch {
                val buffer = CharArray(1024)
                while (true) {
                    val size =
                        Win32Api.getActiveWindowTitleB(buffer) ?: continue
                    trySend(transform(buffer, size))
                    delay(sampleInterval)
                }
            }
            awaitClose {
                job.cancel()
            }
        }.distinctUntilChanged()
    }
}
