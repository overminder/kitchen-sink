package macrocore

import kotlinx.coroutines.flow.Flow
import kotlin.time.Duration

/**
 * Mouse button constants.
 */
enum class MouseButton { Left, Right }

/**
 * A point on the screen.
 */
data class ScreenPoint(val x: Int, val y: Int)

/**
 * An RGB color.
 */
data class ScreenColor(val r: Int, val g: Int, val b: Int) {
    fun distanceTo(other: ScreenColor): Double {
        val dr = (r - other.r).toDouble()
        val dg = (g - other.g).toDouble()
        val db = (b - other.b).toDouble()
        return kotlin.math.sqrt(dr * dr + dg * dg + db * db)
    }
}

// -- Input interfaces --

/**
 * Keyboard input: key press/release events as Flow.
 */
interface KeyboardInput {
    fun keyPresses(): Flow<String>
    fun keyReleases(): Flow<String>
}

/**
 * Keyboard output: post key press/release events.
 */
interface KeyboardOutput {
    fun postPress(keyCode: String)
    fun postRelease(keyCode: String)
}

/**
 * Mouse input: mouse move/click events as Flow.
 */
interface MouseInput {
    fun clickEvents(): Flow<ScreenPoint>
    fun motionEvents(): Flow<ScreenPoint>
}

/**
 * Mouse output: post mouse move/click events.
 */
interface MouseOutput {
    fun moveTo(point: ScreenPoint)
    suspend fun postClick(
        point: ScreenPoint,
        button: MouseButton = MouseButton.Left,
        delayMs: Long = 50,
        moveFirst: Boolean = false,
    )
}

/**
 * Clipboard read/write.
 */
interface Clipboard {
    fun getText(): String?
    fun setText(text: String)
}

/**
 * Screen capture: read pixel colors at coordinates.
 */
interface Screen {
    fun getPixelColor(point: ScreenPoint): ScreenColor
    fun captureScreen(): PixelSource
}

/**
 * A captured screen image for batch pixel reads.
 */
interface PixelSource {
    fun getPixelColor(point: ScreenPoint): ScreenColor
}

/**
 * Checks whether a given window title matches the current foreground window.
 */
interface ActiveWindowChecker {
    fun isActiveWindow(title: String): Boolean
}

/**
 * Clock: current time and delay, abstracted for testable timing.
 */
interface Clock {
    fun currentTimeMillis(): Long
    suspend fun delay(duration: Duration, extraVarianceMs: Long = 10)
}
