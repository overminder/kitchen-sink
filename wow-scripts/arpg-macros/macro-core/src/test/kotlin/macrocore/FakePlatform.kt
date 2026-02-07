package macrocore

import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.MutableSharedFlow
import kotlin.time.Duration

/**
 * Fake keyboard input for testing. Emits events via [emitPress] and [emitRelease].
 */
class FakeKeyboardInput : KeyboardInput {
    private val presses = MutableSharedFlow<String>(extraBufferCapacity = 64)
    private val releases = MutableSharedFlow<String>(extraBufferCapacity = 64)

    override fun keyPresses(): Flow<String> = presses
    override fun keyReleases(): Flow<String> = releases

    suspend fun emitPress(key: String) = presses.emit(key)
    suspend fun emitRelease(key: String) = releases.emit(key)
}

/**
 * Recording keyboard output for testing. Records all posted key events.
 */
class FakeKeyboardOutput : KeyboardOutput {
    data class Event(val keyCode: String, val pressed: Boolean)

    val events = mutableListOf<Event>()

    override fun postPress(keyCode: String) {
        events += Event(keyCode, pressed = true)
    }

    override fun postRelease(keyCode: String) {
        events += Event(keyCode, pressed = false)
    }
}

/**
 * Fake mouse input for testing.
 */
class FakeMouseInput : MouseInput {
    private val clicks = MutableSharedFlow<ScreenPoint>(extraBufferCapacity = 64)
    private val motions = MutableSharedFlow<ScreenPoint>(extraBufferCapacity = 64)

    override fun clickEvents(): Flow<ScreenPoint> = clicks
    override fun motionEvents(): Flow<ScreenPoint> = motions

    suspend fun emitClick(point: ScreenPoint) = clicks.emit(point)
    suspend fun emitMotion(point: ScreenPoint) = motions.emit(point)
}

/**
 * Recording mouse output for testing. Records all mouse actions.
 */
class FakeMouseOutput : MouseOutput {
    sealed class Action {
        data class MoveTo(val point: ScreenPoint) : Action()
        data class Click(
            val point: ScreenPoint,
            val button: MouseButton,
            val moveFirst: Boolean,
        ) : Action()
    }

    val actions = mutableListOf<Action>()

    override fun moveTo(point: ScreenPoint) {
        actions += Action.MoveTo(point)
    }

    override suspend fun postClick(
        point: ScreenPoint,
        button: MouseButton,
        delayMs: Long,
        moveFirst: Boolean,
    ) {
        actions += Action.Click(point, button, moveFirst)
    }
}

/**
 * Fake clipboard for testing.
 */
class FakeClipboard : Clipboard {
    var content: String? = null

    override fun getText(): String? = content
    override fun setText(text: String) {
        content = text
    }
}

/**
 * Fake screen for testing. Returns colors from a configurable map.
 */
class FakeScreen : Screen {
    var pixels: Map<ScreenPoint, ScreenColor> = emptyMap()
    var defaultColor = ScreenColor(0, 0, 0)

    override fun getPixelColor(point: ScreenPoint): ScreenColor {
        return pixels[point] ?: defaultColor
    }

    override fun captureScreen(): PixelSource {
        val snapshot = pixels.toMap()
        val default = defaultColor
        return object : PixelSource {
            override fun getPixelColor(point: ScreenPoint): ScreenColor {
                return snapshot[point] ?: default
            }
        }
    }
}

/**
 * Fake active window checker for testing.
 */
class FakeActiveWindowChecker : ActiveWindowChecker {
    var activeTitle: String = ""
    override fun isActiveWindow(title: String) = activeTitle == title
}

/**
 * Fake clock for testing. Time advances only when explicitly told to.
 */
class FakeClock : Clock {
    var now: Long = 0L

    override fun currentTimeMillis(): Long = now

    override suspend fun delay(duration: Duration, extraVarianceMs: Long) {
        now += duration.inWholeMilliseconds
    }

    fun advance(millis: Long) {
        now += millis
    }
}
