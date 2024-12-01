@file:OptIn(FlowPreview::class)

package com.gh.om.gamemacros

import com.github.kwhat.jnativehook.keyboard.NativeKeyEvent
import kotlinx.coroutines.FlowPreview
import kotlinx.coroutines.async
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.joinAll
import java.awt.Color
import java.time.Duration
import java.time.Instant
import kotlin.math.pow

object GameSpecific {
    val ALL = listOf(
        // ::triggerSkillsInD4,
        ::townHotkeyInPoe,
        ::autoFlaskInPoe,
        ::tripleClickInPoe,
        // ::novaOfFrostboltsInPoe,
        // ::detonateMineInPoe,
    )

    private suspend fun triggerSkillsInD4() {
        val shouldTrigger = combine(
            KeyHooks.keyStates(),
            ScreenCommons.INSTANCE.activeWindowHas(title = "Diablo IV")
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
            safeDelay(Duration.ofMillis(10))
        }
    }

    /**
     * Triggers both ice nova and frostbolts with just one key. This
     * allows us to emulate Kitava's Thirst while still benefitting from
     * suppressions from a rare helmet.
     *
     * Warning: This (or manual self-casting frostbolt in general) will
     * result in 30-50% less DPS, because of the zero dps frostbolt cast.
     */
    private suspend fun novaOfFrostboltsInPoe() {
        val isPoe = isPoeAndTriggerKeyEnabled()
        val inputKey = "E"
        // Comes from POB.
        val frostboltCastRate = 4.53
        // Can be slower than what POB shows
        val novaCastRate = 6.36
        val sequencer = KeySequencer.from(
            listOf(
                // Need to cast frostbolt first, so spell echo from nova
                // goes to the frostbolt (instead of on the self-cast,
                // which incurs double backswing animation)
                "F" to frostboltCastRate,
                "D" to novaCastRate,
                "D" to novaCastRate,
                "D" to novaCastRate,
            )
        )

        // The idea is to consider both discrete input key presses and
        // continuous input key states, and continuously run the key
        // sequence while the input key is pressed.
        KeyHooksEx
            .keyPressed(inputKey, sampleInterval = null)
            .onStart { emit(false) }
            .collectLatest { pressed ->
                while (isPoe.value && pressed) {
                    sequencer()
                }
            }
    }

    /**
     * Detonate mines after each throw
     */
    private suspend fun detonateMineInPoe() {
        val isPoe = isPoeAndTriggerKeyEnabled()
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
            safeDelay(Duration.ofMillis(100))
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

    private suspend fun tripleClickInPoe() {
        val mousePosition = MouseHooks
            .motionEvents()
            .map {
                it.x to it.y
            }
            .stateIn(currentCoroutineScope())

        val isPoe = isPoe()
        suspend fun handle(pressed: Boolean) {
            if (!isPoe.value || !pressed) {
                return
            }

            repeat(3) {
                val (x, y) = mousePosition.value
                MouseHooks.postClick(x, y)
                safeDelay(Duration.ofMillis(16))
            }
        }
        KeyHooksEx.keyPressed("X", sampleInterval = null).collect(::handle)
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
        val skillKeys = setOf("Q", "E")
        // val skillKeys = setOf("Q", "E", "W")

        val fm = BuffManager(PoeFlasks.mbTincture.toKeeper())

        val isPoe = isPoeAndTriggerKeyEnabled()

        val flaskInputs = combine(
            isPoe, KeyHooks.keyStates()
        ) { isPoe, keyState ->
            PoeFlasks.InputEvent(
                timestamp = Instant.now(),
                shouldUse = isPoe && skillKeys.any(keyState.pressed::contains)
            )
        }

        val flaskInputState = flaskInputs.stateIn(currentCoroutineScope())

        val gapFixer = currentCoroutineScope().async {
            PoeFlasks.runGapFixer(fm, flaskInputs, isPoe)
        }

        val useWhenKeyDown = currentCoroutineScope().async {
            KeyHooks.keyPresses().collect {
                if (it in skillKeys && isPoe.value) {
                    fm.useAll()
                }
            }
        }


        val useWhenLongPressed = currentCoroutineScope().async {
            while (true) {
                if (flaskInputState.value.shouldUse) {
                    fm.useAll()
                }
                safeDelay(Duration.ofMillis(100))
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
    val leveling2Qs = Config.alt(4, 5)
    val leveling3Qs = Config.alt(3, 4, 5)
    val leveling2Qs1U =
        Config.Par(
            listOf(
                // Config.One(2),
                Config.One(3),
                Config.alt(4, 5)
            )
        )
    val leveling2Qs2U =
        Config.Par(
            listOf(
                Config.One(2),
                Config.One(3),
                Config.alt(4, 5)
            )
        )
    val all = Config.par(1, 2, 3, 4, 5)
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

    val nonPf = Config.par(2, 3, 4, 5)
    val mbTincture = Config.One(3, isTincture = true)

    // Leftmost pixel of buff bar for each flask in 2560x1440 resolution
    private val X_COORDS = listOf(
        416,
        477,
        539,
        600,
        661,
    ).map { it + 2 /* To use flasks slightly earlier */ }
    private val Y_COORD = 1432

    // Tinctures have a different "active" pixel checking logic,
    // though their "cooldown" bar looks like flask's duration bar.
    private val TINCTURE_X = 444
    private val TINCTURE_Y = 1314

    // The color for flask's duration bar (or tincture's cooldown bar)
    private val BUFF_COLOR = Color(249, 215, 153)

    // The color for tincture's red light activation indicator at the top
    private val TINCTURE_ACTIVE_COLOR = Color(164, 83, 40)

    fun tinctureKeeper(
        ix: Int
    ): BuffKeeper {
        val activeX = X_COORDS[ix] + TINCTURE_X - X_COORDS.first()
        val activeY = TINCTURE_Y
        val isCoolingDown = { isDurationBarActive(ix) }

        fun doUse() = KeyHooks.postAsciiString("${ix + 1}")

        fun isActiveOrCoolingDown(): Boolean {
            val pixel =
                ScreenCommons.INSTANCE.getPixel(x = activeX, y = activeY)
                    ?: return false
            val distance = colorDistance(TINCTURE_ACTIVE_COLOR, pixel)
            // println("Pixel: $pixel, distance = $distance")
            val isActive = distance < 15
            return isActive || isCoolingDown()
        }

        return SingleBuffKeeper(
            applyBuff = ::doUse,
            isBuffInEffect = ::isActiveOrCoolingDown
        )
    }

    fun flaskKeeper(
        flaskIx: Int,
    ): BuffKeeper {
        fun useFlask() = KeyHooks.postAsciiString("${flaskIx + 1}")

        return SingleBuffKeeper(
            applyBuff = ::useFlask,
            isBuffInEffect = { isDurationBarActive(flaskIx) }
        )
    }

    private fun isDurationBarActive(ix: Int): Boolean {
        val x = X_COORDS[ix]
        val y = Y_COORD
        val pixel = ScreenCommons.INSTANCE.getPixel(x = x, y = y)
            ?: return false

        return colorDistance(BUFF_COLOR, pixel) < 10
    }

    data class InputEvent(
        val timestamp: Instant,
        val shouldUse: Boolean,
    )

    /**
     * The index of the flask slot.
     */
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
        data class One(
            val key: Int,
            val isTincture: Boolean = false
        ) : Config()

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

                is One -> if (isTincture) {
                    tinctureKeeper(key - 1)
                } else {
                    flaskKeeper(key - 1)
                }
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
    .INSTANCE
    .activeWindowHas(title = title)
    .onStart { emit(false) }
    .stateIn(currentCoroutineScope())

private suspend fun isPoe() = activeTitleAsState("Path of Exile")

private suspend fun isPoeAndTriggerKeyEnabled(): StateFlow<Boolean> {
    return combine(
        isPoe(), isTriggerKeyEnabled(),
    ) { isPoe, enabled ->
        isPoe && enabled
    }.stateIn(currentCoroutineScope())
}

private suspend fun isTriggerKeyEnabled(
    keyToDisable: String = "F4"
): Flow<Boolean> {
    val disabledSince = KeyHooks.keyPresses().mapNotNull {
        // Key to temporarily disable triggers
        if (it == keyToDisable) {
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

    return disabledSince
        .sampleAndReemit(Duration.ofSeconds(1))
        .map { disabledSince ->
            val now = Instant.now()
            disabledSince == null || now.isAfter(
                disabledSince.plusSeconds(10)
            )
        }
}

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
