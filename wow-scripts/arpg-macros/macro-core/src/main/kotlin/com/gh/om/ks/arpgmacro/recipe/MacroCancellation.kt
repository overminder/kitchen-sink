package com.gh.om.ks.arpgmacro.recipe

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.combine
import kotlinx.coroutines.flow.filter
import kotlinx.coroutines.flow.flow
import kotlinx.coroutines.flow.onStart
import kotlinx.coroutines.flow.stateIn
import kotlinx.coroutines.flow.transformLatest
import kotlinx.coroutines.isActive
import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.GlobalMacroConfig
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.di.GameType
import javax.inject.Inject
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds

object GameTitles {
    val ALL_POE = GameType.ALL_POE.map(::from)

    fun from(gameType: GameType): String {
        return when (gameType) {
            GameType.POE1 -> "Path of Exile"
            GameType.POE2 -> "Path of Exile 2"
            GameType.Diablo3 -> "Diablo 3"
            GameType.Diablo4 -> "Diablo IV"
        }
    }
}

/**
 * Polls ActiveWindowChecker and emits whether the given title is the foreground window.
 */
fun ActiveWindowChecker.activeWindowFlow(
    anyTitles: Collection<String>,
    interval: Duration = 100.milliseconds,
): Flow<Boolean> = flow {
    while (currentCoroutineContext().isActive) {
        emit(isActiveWindow(anyTitles))
        delay(interval)
    }
}

/**
 * Emits false for [disableDuration] after any key in [keys] is pressed, true otherwise.
 * Same semantics as old isTriggerKeyEnabled().
 */
@OptIn(ExperimentalCoroutinesApi::class)
fun KeyboardInput.triggerKeyEnabledFlow(
    keys: Set<String>,
    disableDuration: Duration = 3.seconds,
): Flow<Boolean> {
    return keyPresses()
        .filter { it in keys }
        .transformLatest {
            emit(false)
            delay(disableDuration)
            emit(true)
        }
        .onStart { emit(true) }
}

class ShouldContinueChecker @Inject constructor(
    private val windowChecker: ActiveWindowChecker,
    private val keyboardInput: KeyboardInput,
    private val config: GlobalMacroConfig,
) {
    suspend fun get(
        anyWindowTitles: Collection<String> = setOf(GameTitles.from(GameType.POE1)),
        stopKeys: Set<String> = setOf(config.stopKey)
    ): StateFlow<Boolean> {
        val windowFlow = windowChecker.activeWindowFlow(anyWindowTitles)
        val keyFlow = keyboardInput.triggerKeyEnabledFlow(stopKeys)
        return combine(windowFlow, keyFlow) { windowActive, keyEnabled ->
            windowActive && keyEnabled
        }.stateIn(CoroutineScope(currentCoroutineContext()))
    }
}
