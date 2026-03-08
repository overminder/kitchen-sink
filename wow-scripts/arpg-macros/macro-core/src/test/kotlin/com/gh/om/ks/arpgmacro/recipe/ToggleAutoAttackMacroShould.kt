@file:OptIn(kotlinx.coroutines.ExperimentalCoroutinesApi::class)

package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
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

// -- Helpers --

private fun TestScope.buildMacro(
    active: Boolean = true,
): Triple<ToggleAutoAttackMacro, FakeKeyboardInput, FakeKeyboardOutput> {
    val kb = FakeKeyboardInput()
    val out = FakeKeyboardOutput()
    val macro = ToggleAutoAttackMacro(
        activeWindowChecker = FakeActiveWindowChecker(active),
        keyboardInput = kb,
        keyboardOutput = out,
        clock = FakeClock(this),
    )
    return Triple(macro, kb, out)
}

// -- Tests --

class ToggleAutoAttackMacroShould {

    @Test
    fun `pressing D starts the W attack loop`() = runTest {
        val (macro, kb, out) = buildMacro()
        val job = launch { macro.run(MutableStateFlow(true)) }
        runCurrent()

        kb.press("D")
        runCurrent() // toggled=true, attack loop fires postPress("W"), then suspends at delay

        assertThat(out.pressed).contains("W")
        job.cancel()
    }

    @Test
    fun `pressing E stops the attack loop and releases W`() = runTest {
        val (macro, kb, out) = buildMacro()
        val job = launch { macro.run(MutableStateFlow(true)) }
        runCurrent()

        kb.press("D")
        runCurrent() // attack loop starts, postPress("W") called, suspends at delay(500ms)

        assertThat(out.pressed).isNotEmpty()

        kb.press("E")
        runCurrent() // toggled=false, collectLatest cancels the attack loop

        // Every W press must have a matching release — no stuck keys.
        assertThat(out.released.count { it == "W" }).isEqualTo(out.pressed.count { it == "W" })

        val pressCount = out.pressed.size
        advanceTimeBy(2_000) // no new W presses should occur
        assertThat(out.pressed.size).isEqualTo(pressCount)

        job.cancel()
    }

    @Test
    fun `pressing D again turns off the attack`() = runTest {
        val (macro, kb, out) = buildMacro()
        val job = launch { macro.run(MutableStateFlow(true)) }
        runCurrent()

        // Toggle on
        kb.press("D")
        runCurrent()
        assertThat(out.pressed).isNotEmpty()

        // Release D so rising-edge detector resets, then press again to toggle off
        kb.release("D")
        runCurrent()
        kb.press("D")
        runCurrent() // toggled=false, attack loop cancelled

        val countAfterToggleOff = out.pressed.size
        advanceTimeBy(2_000)

        assertThat(out.pressed.size).isEqualTo(countAfterToggleOff)
        job.cancel()
    }

    @Test
    fun `D press is ignored when window is not active`() = runTest {
        val (macro, kb, out) = buildMacro(active = false)
        val job = launch { macro.run(MutableStateFlow(true)) }
        runCurrent()

        kb.press("D")
        runCurrent()
        advanceTimeBy(2_000)

        assertThat(out.pressed).isEmpty()
        job.cancel()
    }

    @Test
    fun `D press is ignored when macro is disabled`() = runTest {
        val (macro, kb, out) = buildMacro()
        val job = launch { macro.run(MutableStateFlow(false)) }
        runCurrent()

        kb.press("D")
        runCurrent()
        advanceTimeBy(2_000)

        assertThat(out.pressed).isEmpty()
        job.cancel()
    }
}
