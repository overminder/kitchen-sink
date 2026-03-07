package com.gh.om.ks.arpgmacro.recipe.poe

import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.Screen
import com.gh.om.ks.arpgmacro.core.ScreenColor
import com.gh.om.ks.arpgmacro.core.ScreenPoint
import com.gh.om.ks.arpgmacro.core.buff.AlternatingBuffKeeper
import com.gh.om.ks.arpgmacro.core.buff.BuffKeeper
import com.gh.om.ks.arpgmacro.core.buff.BuffManager
import com.gh.om.ks.arpgmacro.core.buff.ParallelBuffKeeper
import com.gh.om.ks.arpgmacro.core.buff.SingleBuffKeeper
import com.gh.om.ks.arpgmacro.core.postAsciiString
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.SharingStarted
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.filter
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.stateIn
import java.time.Duration
import java.time.Instant

object PoeFlasks {
    // Predefined configs
    val leveling1Qs = Config.alt(3)
    val leveling2Qs = Config.alt(4, 5)
    val leveling3Qs = Config.alt(3, 4, 5)
    val leveling4Qs = Config.alt(2, 3, 4, 5)
    val leveling2Qs1U = Config.Par(listOf(Config.One(3), Config.alt(4, 5)))
    val boss3Qs = Config.Par(listOf(Config.One(1), Config.One(2), Config.alt(3, 4, 5)))
    val leveling2Qs2U = Config.Par(listOf(Config.One(2), Config.One(3), Config.alt(4, 5)))
    val all = Config.par(1, 2, 3, 4, 5)
    val dualLife = Config.Par(
        listOf(Config.alt(1, 2), Config.One(3), Config.One(4), Config.One(5))
    )
    val nonPf2 = Config.par(4, 5)
    val nonPf3 = Config.par(3, 4, 5)
    val nonPf = Config.par(2, 3, 4, 5)
    val mbTincture = Config.One(3, isTincture = true)

    val allConfigs: List<Pair<String, Config>> = listOf(
        "mbTincture" to mbTincture,
        "all" to all,
        "dualLife" to dualLife,
        "nonPf" to nonPf,
        "nonPf3" to nonPf3,
        "nonPf2" to nonPf2,
        "leveling2Qs1U" to leveling2Qs1U,
        "leveling2Qs2U" to leveling2Qs2U,
        "leveling1Qs" to leveling1Qs,
        "leveling2Qs" to leveling2Qs,
        "leveling3Qs" to leveling3Qs,
        "boss3Qs" to boss3Qs,
    )

    // Leftmost pixel of buff bar for each flask in 2560x1440 resolution
    private val X_COORDS = listOf(416, 477, 539, 600, 661).map { it + 2 /* Use slightly earlier */ }
    private val Y_COORD = 1432

    // Tinctures have a different "active" pixel checking logic
    private val TINCTURE_X = 444
    private val TINCTURE_Y = 1314

    // The color for flask's duration bar (or tincture's cooldown bar)
    private val BUFF_COLOR = ScreenColor(249, 215, 153)

    // The color for tincture's red light activation indicator at the top
    private val TINCTURE_ACTIVE_COLOR = ScreenColor(164, 83, 40)

    fun flaskKeeper(flaskIx: Int, screen: Screen, keyboardOutput: KeyboardOutput, clock: Clock): BuffKeeper {
        return SingleBuffKeeper(
            clock = clock,
            applyBuff = {
                println("[PoeFlasks] pressing flask key ${flaskIx + 1}")
                keyboardOutput.postAsciiString("${flaskIx + 1}")
            },
            isBuffInEffect = { isDurationBarActive(flaskIx, screen) },
        )
    }

    fun tinctureKeeper(ix: Int, screen: Screen, keyboardOutput: KeyboardOutput, clock: Clock): BuffKeeper {
        val activeX = X_COORDS[ix] + TINCTURE_X - X_COORDS.first()
        val activeY = TINCTURE_Y

        return SingleBuffKeeper(
            clock = clock,
            applyBuff = {
                println("[PoeFlasks] pressing tincture key ${ix + 1}")
                keyboardOutput.postAsciiString("${ix + 1}")
            },
            isBuffInEffect = {
                val pixel = screen.getPixelColor(ScreenPoint(activeX, activeY))
                val isActive = TINCTURE_ACTIVE_COLOR.distanceTo(pixel) < 15
                isActive || isDurationBarActive(ix, screen)
            },
        )
    }

    private fun isDurationBarActive(ix: Int, screen: Screen): Boolean {
        val x = X_COORDS[ix]
        val y = Y_COORD
        val pixel = screen.getPixelColor(ScreenPoint(x, y))
        return BUFF_COLOR.distanceTo(pixel) < 10
    }

    data class InputEvent(
        val timestamp: Instant,
        val shouldUse: Boolean,
    )

    /**
     * Represents a group of flasks, automated in a certain way.
     */
    sealed class Config {
        data class Alt(val configs: List<Config>) : Config()
        data class One(val key: Int, val isTincture: Boolean = false) : Config()
        data class Par(val configs: List<Config>) : Config()

        fun toKeeper(screen: Screen, keyboardOutput: KeyboardOutput, clock: Clock): BuffKeeper {
            return when (this) {
                is Alt -> AlternatingBuffKeeper(
                    keepers = configs.map { it.toKeeper(screen, keyboardOutput, clock) },
                    clock = clock,
                )
                is Par -> ParallelBuffKeeper(
                    keepers = configs.map { it.toKeeper(screen, keyboardOutput, clock) },
                )
                is One -> if (isTincture) {
                    tinctureKeeper(key - 1, screen, keyboardOutput, clock)
                } else {
                    flaskKeeper(key - 1, screen, keyboardOutput, clock)
                }
            }
        }

        companion object {
            fun alt(vararg keys: Int): Config = Alt(keys.map(::One))
            fun par(vararg keys: Int): Config = Par(keys.map(::One))
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
            .stateIn(
                scope = CoroutineScope(currentCoroutineContext()),
                started = SharingStarted.Eagerly,
                initialValue = Instant.EPOCH,
            )

        buffManager.runGapFixer(
            getTimestampForActivePlaying = activelyPlaying::value,
            isGameActive = isPoe::value,
        )
    }
}
