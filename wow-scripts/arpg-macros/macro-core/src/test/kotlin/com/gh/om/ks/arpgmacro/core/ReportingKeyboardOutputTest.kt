package com.gh.om.ks.arpgmacro.core

import com.gh.om.ks.arpgmacro.core.overlay.BgMacroEventSink
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test

class ReportingKeyboardOutputTest {

    private val delegate = FakeKeyboardOutput()
    private val sink = FakeBgMacroEventSink()

    @Test
    fun `posts keys when not suppressed`() {
        val output = ReportingKeyboardOutput("flask", delegate, sink) { false }

        output.postPress("5")
        output.postRelease("5")

        assertThat(delegate.events).containsExactly(
            FakeKeyboardOutput.Event("5", pressed = true),
            FakeKeyboardOutput.Event("5", pressed = false),
        )
        assertThat(sink.events).containsExactly("flask:5")
    }

    @Test
    fun `suppresses key output when overlay is open`() {
        var suppressed = false
        val output = ReportingKeyboardOutput("flask", delegate, sink) { suppressed }

        // Keys pass through initially
        output.postPress("5")
        assertThat(delegate.events).hasSize(1)

        // Overlay opens — keys are suppressed
        suppressed = true
        output.postPress("3")
        output.postRelease("3")
        assertThat(delegate.events).hasSize(1) // no new events

        // Overlay closes — keys pass through again
        suppressed = false
        output.postPress("4")
        assertThat(delegate.events).containsExactly(
            FakeKeyboardOutput.Event("5", pressed = true),
            FakeKeyboardOutput.Event("4", pressed = true),
        )
    }

    @Test
    fun `sink does not record suppressed events`() {
        val output = ReportingKeyboardOutput("flask", delegate, sink) { true }

        output.postPress("5")

        assertThat(sink.events).isEmpty()
    }
}

private class FakeBgMacroEventSink : BgMacroEventSink {
    val events = mutableListOf<String>()
    override fun onKeyPress(macroName: String, key: String) {
        events += "$macroName:$key"
    }
}
