package macroapp

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
import macrocore.ActiveWindowChecker
import macrocore.KeyboardInput
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds

/**
 * Polls ActiveWindowChecker and emits whether the given title is the foreground window.
 */
fun ActiveWindowChecker.activeWindowFlow(
    title: String,
    interval: Duration = 100.milliseconds,
): Flow<Boolean> = flow {
    while (currentCoroutineContext().isActive) {
        emit(isActiveWindow(title))
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

/**
 * Combines active-window check and stop-key into a single StateFlow<Boolean>.
 * Read .value as shouldContinue. Same pattern as old isPoeAndTriggerKeyEnabled().
 */
suspend fun macroEnabledFlow(
    windowChecker: ActiveWindowChecker,
    keyboardInput: KeyboardInput,
    windowTitle: String = "Path of Exile",
    stopKeys: Set<String> = setOf("F4"),
): StateFlow<Boolean> {
    val windowFlow = windowChecker.activeWindowFlow(windowTitle)
    val keyFlow = keyboardInput.triggerKeyEnabledFlow(stopKeys)
    return combine(windowFlow, keyFlow) { windowActive, keyEnabled ->
        windowActive && keyEnabled
    }.stateIn(CoroutineScope(currentCoroutineContext()))
}
