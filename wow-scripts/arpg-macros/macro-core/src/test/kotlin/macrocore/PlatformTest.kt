package macrocore

import kotlinx.coroutines.flow.first
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.runTest
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test

class PlatformTest {
    @Test
    fun `FakeKeyboardInput emits presses`() = runTest {
        val kb = FakeKeyboardInput()
        launch { kb.emitPress("A") }
        val key = kb.keyPresses().first()
        assertThat(key).isEqualTo("A")
    }

    @Test
    fun `FakeKeyboardInput emits releases`() = runTest {
        val kb = FakeKeyboardInput()
        launch { kb.emitRelease("X") }
        val key = kb.keyReleases().first()
        assertThat(key).isEqualTo("X")
    }

    @Test
    fun `FakeKeyboardOutput records events`() {
        val kb = FakeKeyboardOutput()
        kb.postPress("Ctrl")
        kb.postRelease("Ctrl")
        assertThat(kb.events).containsExactly(
            FakeKeyboardOutput.Event("Ctrl", pressed = true),
            FakeKeyboardOutput.Event("Ctrl", pressed = false),
        )
    }

    @Test
    fun `FakeMouseOutput records actions`() = runTest {
        val mouse = FakeMouseOutput()
        val p = ScreenPoint(100, 200)
        mouse.moveTo(p)
        mouse.postClick(p, MouseButton.Left, moveFirst = true)
        assertThat(mouse.actions).hasSize(2)
        assertThat(mouse.actions[0]).isEqualTo(FakeMouseOutput.Action.MoveTo(p))
        assertThat(mouse.actions[1]).isEqualTo(
            FakeMouseOutput.Action.Click(p, MouseButton.Left, moveFirst = true)
        )
    }

    @Test
    fun `FakeClipboard stores and returns text`() {
        val clip = FakeClipboard()
        assertThat(clip.getText()).isNull()
        clip.setText("hello")
        assertThat(clip.getText()).isEqualTo("hello")
    }

    @Test
    fun `FakeScreen returns configured pixel colors`() {
        val screen = FakeScreen()
        val p = ScreenPoint(10, 20)
        screen.pixels = mapOf(p to ScreenColor(255, 0, 0))
        assertThat(screen.getPixelColor(p)).isEqualTo(ScreenColor(255, 0, 0))
        assertThat(screen.getPixelColor(ScreenPoint(0, 0))).isEqualTo(ScreenColor(0, 0, 0))
    }

    @Test
    fun `FakeScreen captureScreen returns snapshot`() {
        val screen = FakeScreen()
        val p = ScreenPoint(10, 20)
        screen.pixels = mapOf(p to ScreenColor(255, 0, 0))
        val source = screen.captureScreen()
        // Changing pixels after capture should not affect the snapshot
        screen.pixels = emptyMap()
        assertThat(source.getPixelColor(p)).isEqualTo(ScreenColor(255, 0, 0))
    }

    @Test
    fun `FakeClock advances time`() = runTest {
        val clock = FakeClock()
        assertThat(clock.currentTimeMillis()).isEqualTo(0)
        clock.advance(1000)
        assertThat(clock.currentTimeMillis()).isEqualTo(1000)
    }

    @Test
    fun `ScreenColor distanceTo calculates correctly`() {
        val a = ScreenColor(0, 0, 0)
        val b = ScreenColor(3, 4, 0)
        assertThat(a.distanceTo(b)).isEqualTo(5.0)
    }
}
