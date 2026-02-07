@file:OptIn(ExperimentalCoroutinesApi::class)

package macrocore

import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.cancelAndJoin
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.advanceUntilIdle
import kotlinx.coroutines.test.runTest
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test
import kotlin.time.Duration.Companion.seconds

class LeaderKeyDetectorTest {
    private val kb = FakeKeyboardInput()
    private val clock = FakeClock()

    private fun detector(timeout: kotlin.time.Duration = 2.seconds) = LeaderKeyDetector(
        leaderKey = setOf("Alt", "X"),
        keyboardInput = kb,
        clock = clock,
        timeout = timeout,
    )

    @Test
    fun `happy path - leader then command activates immediately`() = runTest {
        val det = detector()
        val results = mutableListOf<Boolean>()

        val job = launch {
            det.isEnabled("11").collect { results += it }
        }
        advanceUntilIdle()

        kb.emitRelease("X")
        kb.emitRelease("Alt")
        kb.emitRelease("1")
        kb.emitRelease("1")
        advanceUntilIdle()

        assertThat(results).containsExactly(true)
        job.cancelAndJoin()
    }

    @Test
    fun `leader in reverse order still works`() = runTest {
        val det = detector()
        val results = mutableListOf<Boolean>()

        val job = launch {
            det.isEnabled("11").collect { results += it }
        }
        advanceUntilIdle()

        kb.emitRelease("Alt")
        kb.emitRelease("X")
        kb.emitRelease("1")
        kb.emitRelease("1")
        advanceUntilIdle()

        assertThat(results).containsExactly(true)
        job.cancelAndJoin()
    }

    @Test
    fun `wrong command emits false`() = runTest {
        val det = detector()
        val results = mutableListOf<Boolean>()

        val job = launch {
            det.isEnabled("11").collect { results += it }
        }
        advanceUntilIdle()

        kb.emitRelease("Alt")
        kb.emitRelease("X")
        kb.emitRelease("2")
        kb.emitRelease("3")
        advanceUntilIdle()

        assertThat(results).containsExactly(false)
        job.cancelAndJoin()
    }

    @Test
    fun `mistyped recovery - can retry after failure`() = runTest {
        val det = detector()
        val results = mutableListOf<Boolean>()

        val job = launch {
            det.isEnabled("11").collect { results += it }
        }
        advanceUntilIdle()

        // First attempt: wrong command
        kb.emitRelease("Alt")
        kb.emitRelease("X")
        kb.emitRelease("2")
        kb.emitRelease("3")
        advanceUntilIdle()
        // Second attempt: correct
        kb.emitRelease("Alt")
        kb.emitRelease("X")
        kb.emitRelease("1")
        kb.emitRelease("1")
        advanceUntilIdle()

        assertThat(results).containsExactly(false, true)
        job.cancelAndJoin()
    }

    @Test
    fun `timeout resets partial sequence`() = runTest {
        val det = detector(timeout = 2.seconds)
        val results = mutableListOf<Boolean>()

        val job = launch {
            det.isEnabled("11").collect { results += it }
        }
        advanceUntilIdle()

        // Type leader
        kb.emitRelease("Alt")
        kb.emitRelease("X")
        advanceUntilIdle()
        // Wait too long
        clock.advance(3000)
        // The next key release triggers the timeout check
        kb.emitRelease("1")
        advanceUntilIdle()

        // Should have emitted false for timeout
        assertThat(results).containsExactly(false)

        // Now re-do from leader
        kb.emitRelease("Alt")
        kb.emitRelease("X")
        kb.emitRelease("1")
        kb.emitRelease("1")
        advanceUntilIdle()

        assertThat(results).containsExactly(false, true)
        job.cancelAndJoin()
    }

    @Test
    fun `stray keys before leader are ignored`() = runTest {
        val det = detector()
        val results = mutableListOf<Boolean>()

        val job = launch {
            det.isEnabled("11").collect { results += it }
        }
        advanceUntilIdle()

        // Stray keys
        kb.emitRelease("A")
        kb.emitRelease("B")
        kb.emitRelease("C")
        advanceUntilIdle()
        // Now actual leader+command
        kb.emitRelease("Alt")
        kb.emitRelease("X")
        kb.emitRelease("1")
        kb.emitRelease("1")
        advanceUntilIdle()

        // Only emitted once (on match), stray keys produced no emissions
        assertThat(results).containsExactly(true)
        job.cancelAndJoin()
    }

    @Test
    fun `multiple commands can be registered independently`() = runTest {
        val det = detector()
        val results1 = mutableListOf<Boolean>()
        val results2 = mutableListOf<Boolean>()

        val job1 = launch {
            det.isEnabled("11").collect { results1 += it }
        }
        val job2 = launch {
            det.isEnabled("22").collect { results2 += it }
        }
        advanceUntilIdle()

        // Trigger command "11"
        kb.emitRelease("Alt")
        kb.emitRelease("X")
        kb.emitRelease("1")
        kb.emitRelease("1")
        advanceUntilIdle()

        assertThat(results1).containsExactly(true)
        // Command "22" should have seen a mismatch
        assertThat(results2).containsExactly(false)

        // Trigger command "22"
        kb.emitRelease("Alt")
        kb.emitRelease("X")
        kb.emitRelease("2")
        kb.emitRelease("2")
        advanceUntilIdle()

        assertThat(results2).contains(true)
        job1.cancelAndJoin()
        job2.cancelAndJoin()
    }
}
