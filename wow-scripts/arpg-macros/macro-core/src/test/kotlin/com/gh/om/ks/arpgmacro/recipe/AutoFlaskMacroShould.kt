@file:OptIn(kotlinx.coroutines.ExperimentalCoroutinesApi::class)

package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.PixelSource
import com.gh.om.ks.arpgmacro.core.Screen
import com.gh.om.ks.arpgmacro.core.ScreenColor
import com.gh.om.ks.arpgmacro.core.ScreenPoint
import com.gh.om.ks.arpgmacro.recipe.poe.PoeFlasks
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.MutableSharedFlow
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.TestScope
import kotlinx.coroutines.test.advanceTimeBy
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test
import kotlin.time.Duration

// -- Fakes --

private class FakeKeyboardInput : KeyboardInput {
    // Buffered so tryEmit never suspends the test coroutine
    private val pressFlow = MutableSharedFlow<String>(extraBufferCapacity = 16)
    private val releaseFlow = MutableSharedFlow<String>(extraBufferCapacity = 16)

    override fun keyPresses(): Flow<String> = pressFlow
    override fun keyReleases(): Flow<String> = releaseFlow

    fun press(key: String) { pressFlow.tryEmit(key) }
    fun release(key: String) { releaseFlow.tryEmit(key) }
}

private class FakeKeyboardOutput : KeyboardOutput {
    val pressed = mutableListOf<String>()
    override fun postPress(key: String) { pressed += key }
    override fun postRelease(key: String) {}
}

private class FakeScreen : Screen {
    // Black pixel is far from BUFF_COLOR(249,215,153), so isDurationBarActive() always returns
    // false, meaning keepers always consider the buff expired and will attempt to trigger.
    override fun getPixelColor(point: ScreenPoint) = ScreenColor(0, 0, 0)
    override fun captureScreen(): PixelSource = throw UnsupportedOperationException()
}

private class FakeClock(private val scope: TestScope) : Clock {
    // Ties wall-clock reads to the test scheduler so throttle logic sees virtual time.
    override fun currentTimeMillis(): Long = scope.testScheduler.currentTime
    override suspend fun delay(duration: Duration, extraVarianceMs: Long) =
        kotlinx.coroutines.delay(duration)
}

private class FakeActiveWindowChecker : ActiveWindowChecker {
    // Always reports the queried game as active (simulates POE in focus).
    override fun isActiveWindow(anyTitles: Collection<String>) = true
}

// -- Tests --

class AutoFlaskMacroShould {

    /**
     * Regression test for the collectLatest scoping bug:
     * async children launched inside collectLatest { } were parented to the outer coroutineScope,
     * so changing the config left the old config's loops (useWhenKeyDown, useWhenLongPressed,
     * gapFixer) running alongside the new ones.
     *
     * After the fix (inner coroutineScope inside collectLatest), switching config must
     * cancel all loops from the previous config before starting the new ones.
     */
    @Test
    fun `pressing W after selectConfig only sends keys from the new config`() = runTest {
        val keyboardInput = FakeKeyboardInput()
        val keyboardOutput = FakeKeyboardOutput()
        val macro = AutoFlaskMacro(
            keyboardInput = keyboardInput,
            keyboardOutput = keyboardOutput,
            activeWindowChecker = FakeActiveWindowChecker(),
            screen = FakeScreen(),
            clock = FakeClock(this),
        )

        val job = launch { macro.run(MutableStateFlow(true)) }

        // Let isPoe / triggerEnabled StateFlows initialize and collectLatest start.
        runCurrent()

        // Default config is mbTincture = Config.One(3, isTincture = true) → sends key "3".
        keyboardInput.press("W")
        runCurrent()
        assertThat(keyboardOutput.pressed).contains("3")

        // Release W so keyStates no longer triggers shouldUse.
        keyboardInput.release("W")
        runCurrent()

        // Switch to leveling2Qs = Config.alt(4, 5) — must only send "4" and "5".
        macro.selectConfig(PoeFlasks.leveling2Qs)
        runCurrent()

        keyboardOutput.pressed.clear()

        // Advance past SingleBuffKeeper's 1-second throttle so the new keepers can fire.
        advanceTimeBy(1_100)
        runCurrent()

        keyboardInput.press("W")
        runCurrent()

        // If the old mbTincture loop survived config switch it would still emit "3" here.
        assertThat(keyboardOutput.pressed).doesNotContain("3")
        assertThat(keyboardOutput.pressed).containsAnyOf("4", "5")

        job.cancel()
    }
}
