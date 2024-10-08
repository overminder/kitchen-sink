@file:OptIn(FlowPreview::class)

package com.gh.om.gamemacros

import com.github.kwhat.jnativehook.keyboard.NativeKeyEvent
import kotlinx.coroutines.FlowPreview
import kotlinx.coroutines.async
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.time.delay
import org.example.com.gh.om.gamemacros.Win32Api
import java.awt.Color
import java.time.Duration
import java.time.Instant
import kotlin.math.pow
import kotlin.random.Random


object GameSpecific {
    val ALL = listOf(
        ::triggerSkillsInD4,
        ::townHotkeyInPoe,
        ::autoFlaskInPoe,
        // ::detonateMineInPoe,
    )

    private suspend fun triggerSkillsInD4() {
        val shouldTrigger = combine(
            KeyHooks.keyStates(),
            ScreenCommons.activeWindowHas(title = "Diablo IV")
        ) { keyState, isD4 ->
            // E is the key for the main skill
            "E" in keyState.pressed && isD4
        }.stateIn(currentCoroutineScope())

        val actions = ActionCombinators.roundRobin(
            // All the rest of the skills to be triggered together
            listOf(
                NativeKeyEvent.VC_Q,
                NativeKeyEvent.VC_2,
                NativeKeyEvent.VC_3,
                NativeKeyEvent.VC_4,
            ).map(::actionToPressAndReleaseKey)
        )

        while (true) {
            if (shouldTrigger.value) {
                actions()
            }
            delay(Duration.ofMillis(10))
        }
    }

    /**
     * Detonate mines after each throw
     */
    private suspend fun detonateMineInPoe() {
        val isPoe = isPoe()
        val mineKey = "E"

        suspend fun detonateWhenThrowing(isThrowingMines: Boolean) {
            if (!isPoe.value || !isThrowingMines) {
                return
            }
            KeyHooks.postPressRelease(NativeKeyEvent.VC_T)
        }

        suspend fun detonateAfterThrowing(thrown: Boolean) {
            if (!isPoe.value || !thrown) {
                return
            }
            delay(Duration.ofMillis(100))
            KeyHooks.postPressRelease(NativeKeyEvent.VC_T)
        }

        currentCoroutineScope().async {
            KeyHooks
                .keyStates()
                .map { mineKey in it.pressed }
                // | Important! Otherwise keyStates are constantly changing
                .distinctUntilChanged()
                .sampleAndReemit(Duration.ofMillis(100))
                .collect(::detonateWhenThrowing)
        }

        KeyHooks
            .keyReleases()
            .map { it == mineKey }
            .collectLatest(::detonateAfterThrowing)
    }

    private suspend fun townHotkeyInPoe() {
        val isPoe = isPoe()

        val hotkeys = mapOf(
            "F5" to "/hideout",
            "F6" to "/kingsmarch",
        )

        fun handle(key: String) {
            if (!isPoe.value) {
                return
            }
            val command = hotkeys[key] ?: return
            KeyHooks.postPressRelease(NativeKeyEvent.VC_ENTER)
            KeyHooks.postAsciiString(command)
            KeyHooks.postPressRelease(NativeKeyEvent.VC_ENTER)
        }

        KeyHooks.keyReleases().collect(::handle)
    }

    private suspend fun autoFlaskInPoe() {
        // Keys to trigger flasks
        // val skillKeys = setOf("Q", "E")
        val skillKeys = setOf("Q", "E", "W")

        val autoFlaskDisabledSince = KeyHooks.keyPresses().mapNotNull {
            // Key to temporarily disable auto flask
            if (it == "F4") {
                // XXX This should come from the original source of the flow,
                // not during a transformation (because flow is lazy)...
                // Otherwise, this flow should be made hot to eagerly pull
                // the current time.
                Instant.now()
            } else {
                null
            }
        }.asNullable()
            .onStart { emit(null) }
            .stateIn(currentCoroutineScope())

        val autoFlaskEnabled = autoFlaskDisabledSince
            .sampleAndReemit(Duration.ofSeconds(1))
            .map { disabledSince ->
                val now = Instant.now()
                disabledSince == null || now.isAfter(
                    disabledSince.plusSeconds(10)
                )
            }

        val isPoeF = combine(
            isPoe(), autoFlaskEnabled,
        ) { isPoe, enabled ->
            isPoe && enabled
        }.stateIn(currentCoroutineScope())

        val flaskInputs = combine(
            isPoeF, KeyHooks.keyStates()
        ) { isPoe, keyState ->
            PoeFlasks.InputEvent(
                timestamp = Instant.now(),
                shouldUse = isPoe && skillKeys.any(keyState.pressed::contains)
            )
        }

        val flaskInputState = flaskInputs.stateIn(currentCoroutineScope())

        val fm = BuffManager(PoeFlasks.leveling.toKeeper())

        val gapFixer = currentCoroutineScope().async {
            PoeFlasks.runGapFixer(fm, flaskInputs, isPoeF)
        }

        val useWhenKeyDown = currentCoroutineScope().async {
            KeyHooks.keyPresses().collect {
                if (it in skillKeys && isPoeF.value) {
                    fm.useAll()
                }
            }
        }


        val useWhenLongPressed = currentCoroutineScope().async {
            while (true) {
                if (flaskInputState.value.shouldUse) {
                    fm.useAll()
                }
                delay(Duration.ofMillis(100 + Random.nextLong(10)))
            }
        }

        // Only useWhenLongPressed: No over-firing
        // gapFixer + useWhenLongPressed: Has over-firing
        // useWhenKeyDown + useWhenLongPressed: Has over-firing
        // Sounds like it's a race condition.
        joinAll(gapFixer, useWhenKeyDown, useWhenLongPressed)
    }
}

private object PoeFlasks {
    val leveling =
        Config.Par(
            listOf(
                // Config.One(2),
                // Config.One(3),
                Config.alt(4, 5),
                // Config.par(3, 4, 5),
            )
        )
    val main = Config.par(1, 2, 3, 4, 5)
    val dualLife = Config.Par(
        listOf(
            Config.alt(1, 2),
            // PoeFlasks.Config.par(1, 2),
            Config.One(3),
            Config.One(4),
            Config.One(5),
            // PoeFlasks.Config.alt(4, 5)
        )
    )

    // Leftmost pixel of buff bar for each flask in 2560x1440 resolution
    private val X_COORDS = listOf(
        416,
        477,
        539,
        600,
        661,
    ).map { it + 2 /* To use flasks slightly earlier */ }
    private val Y_COORD = 1432

    private val BUFF_COLOR = Color(249, 215, 153)

    fun flaskKeeper(flaskIx: Int): BuffKeeper {
        val x = X_COORDS[flaskIx]

        fun isBuffActive(): Boolean {
            val pixelRef = Win32Api.getPixel(
                x = x,
                y = Y_COORD
            ) ?: return false
            val pixel = fromColorRef(pixelRef)

            return colorDistance(BUFF_COLOR, pixel) < 10
        }

        fun useFlask() = KeyHooks.postAsciiString("${flaskIx + 1}")

        return SingleBuffKeeper(
            applyBuff = ::useFlask,
            isBuffInEffect = ::isBuffActive
        )
    }

    data class InputEvent(
        val timestamp: Instant,
        val shouldUse: Boolean,
    )

    enum class Ix(val key: Int) {
        F1(0),
        F2(1),
        F3(2),
        F4(3),
        F5(4);
    }

    /**
     * Represents a group of flasks, automated in certain way
     */
    sealed class Config {
        data class Alt(val configs: List<Config>) : Config()
        data class One(val key: Int) : Config()
        data class Par(val configs: List<Config>) : Config()

        fun toKeeper(): BuffKeeper {
            return when (this) {
                is Alt ->
                    AlternatingBuffKeeper(
                        configs.map(Config::toKeeper)
                    )

                is Par ->
                    ParallelBuffKeeper(
                        configs.map(Config::toKeeper)
                    )

                is One -> flaskKeeper(key - 1)
            }
        }

        companion object {
            fun alt(vararg keys: Int): Config {
                return Alt(keys.map(::One))
            }

            fun par(vararg keys: Int): Config {
                return Par(keys.map(::One))
            }
        }
    }

    suspend fun runGapFixer(
        buffManager: BuffManager,
        flaskInputs: Flow<InputEvent>,
        isPoe: StateFlow<Boolean>,
    ) {

        val activelyPlaying = flaskInputs
            .filter { it.shouldUse }
            .map { it.timestamp }
            .stateIn(currentCoroutineScope())

        buffManager.runGapFixer(
            activelyPlaying::value,
            isPoe::value,
        )
    }
}

private fun actionToPressAndReleaseKey(
    keyCode: Int,
    maximumFrequency: Duration = Duration.ofMillis(100)
): () -> Unit =
    ActionCombinators.unconditionallySkipIfTooFrequent(maximumFrequency) {
        KeyHooks.postPressRelease(keyCode)
    }

private suspend fun activeTitleAsState(title: String) = ScreenCommons
    .activeWindowHas(title = title)
    .stateIn(currentCoroutineScope())

private suspend fun isPoe() = activeTitleAsState("Path of Exile")

private val COLOR_RGB_COMPONENTS =
    listOf(Color::getRed, Color::getBlue, Color::getGreen)

private fun colorDistance(
    c1: Color,
    c2: Color
): Double {
    val variances = COLOR_RGB_COMPONENTS.sumOf { comp ->
        (comp(c1) - comp(c2)).toDouble().pow(2)
    }
    return (variances / 3).pow(0.5)
}

// See https://learn.microsoft.com/en-us/windows/win32/gdi/colorref
private fun fromColorRef(colorRef: Int): Color {
    val r = colorRef and 0xff
    val g = (colorRef shr 8) and 0xff
    val b = (colorRef shr 16) and 0xff
    return Color(r, g, b)
}
