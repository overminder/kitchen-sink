package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.FakeClock
import com.gh.om.ks.arpgmacro.core.FakeKeyboardOutput
import com.gh.om.ks.arpgmacro.core.ReportingKeyboardOutput
import com.gh.om.ks.arpgmacro.core.overlay.BgMacroStatusTracker
import com.gh.om.ks.arpgmacro.core.postPressRelease
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test

class BgMacroStatusTrackerShould {

    // -- BgMacroStatusTracker tests --

    @Test
    fun `single event produces one status line`() {
        val tracker = BgMacroStatusTracker(FakeClock())
        tracker.onKeyPress("flask", "3")
        val lines = tracker.status.value
        assertThat(lines).hasSize(1)
        assertThat(lines[0].macroName).isEqualTo("flask")
        assertThat(lines[0].keyCounts).containsExactly("3" to 1)
    }

    @Test
    fun `multiple keys same macro sorted by count descending`() {
        val tracker = BgMacroStatusTracker(FakeClock())
        repeat(3) { tracker.onKeyPress("flask", "3") }
        tracker.onKeyPress("flask", "2")
        val counts = tracker.status.value[0].keyCounts
        assertThat(counts).containsExactly("3" to 3, "2" to 1)
    }

    @Test
    fun `multiple macros produce separate status lines`() {
        val tracker = BgMacroStatusTracker(FakeClock())
        tracker.onKeyPress("flask", "3")
        tracker.onKeyPress("focus", "R")
        assertThat(tracker.status.value.map { it.macroName })
            .containsExactlyInAnyOrder("flask", "focus")
    }

    @Test
    fun `sliding window eviction clears status after 15s`() {
        val clock = FakeClock()
        val tracker = BgMacroStatusTracker(clock)
        tracker.onKeyPress("flask", "3")
        clock.advance(15_001L)
        tracker.tick()
        assertThat(tracker.status.value).isEmpty()
    }

    @Test
    fun `partial eviction keeps only recent events in counts`() {
        val clock = FakeClock()
        val tracker = BgMacroStatusTracker(clock)
        tracker.onKeyPress("flask", "2")  // t=0
        clock.advance(10_000L)
        tracker.onKeyPress("flask", "3")  // t=10s
        tracker.onKeyPress("flask", "3")  // t=10s
        clock.advance(6_000L)             // t=16s; cutoff=1s; t=0 event evicted
        tracker.tick()
        val counts = tracker.status.value[0].keyCounts
        assertThat(counts).containsExactly("3" to 2)
        assertThat(counts.map { it.first }).doesNotContain("2")
    }

    @Test
    fun `running duration is time since first event`() {
        val clock = FakeClock()
        val tracker = BgMacroStatusTracker(clock)
        // Emit continuously every 10s to keep the macro alive
        tracker.onKeyPress("flask", "3")      // t=0, firstSeen=0
        clock.advance(10_000L)
        tracker.onKeyPress("flask", "3")      // t=10s
        clock.advance(10_000L)
        tracker.onKeyPress("flask", "3")      // t=20s
        clock.advance(10_000L)
        tracker.onKeyPress("flask", "3")      // t=30s
        clock.advance(10_000L)
        tracker.onKeyPress("flask", "3")      // t=40s
        clock.advance(10_000L)
        tracker.onKeyPress("flask", "3")      // t=50s
        assertThat(tracker.status.value[0].runningDurationSecs).isEqualTo(50L)
    }

    @Test
    fun `running duration resets after gap longer than window`() {
        val clock = FakeClock()
        val tracker = BgMacroStatusTracker(clock)
        tracker.onKeyPress("flask", "3")      // t=0, firstSeen=0
        clock.advance(20_000L)                // 20s gap > 15s window
        tracker.onKeyPress("flask", "3")      // t=20s, hadRecentEvents=false → firstSeen reset
        assertThat(tracker.status.value[0].runningDurationSecs).isEqualTo(0L)
    }

    // -- ReportingKeyboardOutput tests --

    @Test
    fun `postPressRelease delegates and reports once`() {
        val clock = FakeClock()
        val tracker = BgMacroStatusTracker(clock)
        val delegate = FakeKeyboardOutput()
        val output = ReportingKeyboardOutput("focus", delegate, tracker)

        output.postPressRelease("R")

        assertThat(delegate.events).containsExactly(
            FakeKeyboardOutput.Event("R", pressed = true),
            FakeKeyboardOutput.Event("R", pressed = false),
        )
        assertThat(tracker.status.value).hasSize(1)
        assertThat(tracker.status.value[0].keyCounts).containsExactly("R" to 1)
    }

    @Test
    fun `postRelease does not report to tracker`() {
        val clock = FakeClock()
        val tracker = BgMacroStatusTracker(clock)
        val delegate = FakeKeyboardOutput()
        val output = ReportingKeyboardOutput("focus", delegate, tracker)

        output.postRelease("R")

        assertThat(delegate.events).containsExactly(
            FakeKeyboardOutput.Event("R", pressed = false),
        )
        assertThat(tracker.status.value).isEmpty()
    }
}
