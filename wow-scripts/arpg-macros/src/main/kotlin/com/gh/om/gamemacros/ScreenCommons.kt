package com.gh.om.gamemacros

import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.callbackFlow
import kotlinx.coroutines.flow.distinctUntilChanged
import kotlinx.coroutines.launch
import kotlinx.coroutines.time.delay
import org.example.com.gh.om.gamemacros.Win32Api
import java.awt.Color
import java.time.Duration
import java.util.*

interface ScreenCommons {
    fun activeWindowHas(
        title: String,
        sampleInterval: Duration = Duration.ofMillis(100),
    ): Flow<Boolean>

    fun activeWindowsThat(
        sampleInterval: Duration = Duration.ofMillis(100),
        predicate: (String) -> Boolean,
    ): Flow<Boolean>

    // Assuming a 2560x1440 screen.
    // HiDPI on Mac will need to scale accordingly.
    fun getPixel(
        x: Int,
        y: Int
    ): Color?

    companion object {
        val INSTANCE = when (OS.CURRENT) {
            OS.Mac -> MacScreenCommons
            OS.Windows -> Win32ScreenCommons
            OS.Linux -> error("Not yet implemented for Linux")
            null -> error("Not yet implemented")
        }
    }
}

object Win32ScreenCommons : ScreenCommons {
    override fun activeWindowHas(
        title: String,
        sampleInterval: Duration
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

    override fun getPixel(
        x: Int,
        y: Int
    ): Color? {
        val pixelRef = Win32Api.getPixel(
            x = x,
            y = y
        ) ?: return null
        return fromColorRef(pixelRef)
    }

    override fun activeWindowsThat(
        sampleInterval: Duration,
        predicate: (String) -> Boolean,
    ): Flow<Boolean> {
        return activeWindowsThat(sampleInterval) { cs, len ->
            predicate(cs.slice(0 until len).joinToString(""))
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

private object MacScreenCommons : ScreenCommons {
    override fun activeWindowHas(
        title: String,
        sampleInterval: Duration
    ): Flow<Boolean> {
        return activeWindowsThat(sampleInterval, title::equals)
    }

    override fun activeWindowsThat(
        sampleInterval: Duration,
        predicate: (String) -> Boolean
    ): Flow<Boolean> {
        return callbackFlow {
            val job = launch {
                val buffer = CharArray(1024)
                while (true) {
                    val activeWindowTitle = MacApi.getActiveWindowTitle()
                    trySend(predicate(activeWindowTitle))
                    delay(sampleInterval)
                }
            }
            awaitClose {
                job.cancel()
            }
        }.distinctUntilChanged()
    }

    override fun getPixel(
        x: Int,
        y: Int
    ): Color {
        // Mac uses HiDPI
        return MacApi.getPixel(x / 2, y / 2)
    }
}

// See https://learn.microsoft.com/en-us/windows/win32/gdi/colorref
private fun fromColorRef(colorRef: Int): Color {
    val r = colorRef and 0xff
    val g = (colorRef shr 8) and 0xff
    val b = (colorRef shr 16) and 0xff
    return Color(r, g, b)
}
