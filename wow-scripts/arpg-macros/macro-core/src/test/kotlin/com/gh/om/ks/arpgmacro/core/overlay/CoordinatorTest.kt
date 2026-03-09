@file:OptIn(ExperimentalCoroutinesApi::class)

package com.gh.om.ks.arpgmacro.core.overlay

import com.gh.om.ks.arpgmacro.core.ScreenPoint
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.flow.MutableSharedFlow
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.advanceUntilIdle
import kotlinx.coroutines.test.runTest
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test

class CoordinatorTest {

    private val focusManager = FakeFocusManager()
    private val overlayController = FakeOverlayController()
    private val macroRegistry = FakeMacroRegistry()
    private val macroRunner = FakeMacroRunner()

    private val visibilityChanges = mutableListOf<Boolean>()

    private fun coordinator() = Coordinator(
        focusManager = focusManager,
        overlayController = overlayController,
        macroRegistry = macroRegistry,
        macroRunner = macroRunner,
        onOverlayVisibilityChanged = { visibilityChanges += it },
    )

    @Test
    fun `leader key opens overlay and selection completes`() = runTest {
        val coord = coordinator()
        assertThat(coord.state).isEqualTo(CoordinatorState.Idle)

        val job = launch { coord.onLeaderKey() }
        advanceUntilIdle()

        // Overlay should be open, waiting for selection
        assertThat(coord.state).isEqualTo(CoordinatorState.Open)
        assertThat(overlayController.awaitSelectionCalls).isEqualTo(1)

        // User cancels
        overlayController.completeSelection(OverlaySelection.Cancelled)
        advanceUntilIdle()
        job.join()

        assertThat(coord.state).isEqualTo(CoordinatorState.Idle)
    }

    @Test
    fun `second leader key while open cancels overlay`() = runTest {
        val coord = coordinator()

        // First leader key opens overlay
        val job = launch { coord.onLeaderKey() }
        advanceUntilIdle()
        assertThat(coord.state).isEqualTo(CoordinatorState.Open)

        // Second leader key should cancel
        coord.onLeaderKey()
        advanceUntilIdle()

        assertThat(overlayController.cancelSelectionCalls).isEqualTo(1)

        // The first onLeaderKey should complete (selection was cancelled)
        job.join()
        assertThat(coord.state).isEqualTo(CoordinatorState.Idle)
    }

    @Test
    fun `leader key during macro running is ignored`() = runTest {
        val coord = coordinator()

        // Open overlay
        val job = launch { coord.onLeaderKey() }
        advanceUntilIdle()

        // Select a macro (runner will suspend on its deferred)
        val macro = macroRegistry.macros.first()
        overlayController.completeSelection(OverlaySelection.Selected(macro))
        advanceUntilIdle()
        assertThat(coord.state).isEqualTo(CoordinatorState.MacroRunning)

        // Leader key during macro run should be ignored
        coord.onLeaderKey()
        advanceUntilIdle()
        assertThat(overlayController.cancelSelectionCalls).isEqualTo(0)
        assertThat(coord.state).isEqualTo(CoordinatorState.MacroRunning)

        // Complete the macro
        macroRunner.completeCurrentRun()
        advanceUntilIdle()
        job.join()

        assertThat(coord.state).isEqualTo(CoordinatorState.Idle)
    }

    @Test
    fun `can reopen overlay after toggle-cancel`() = runTest {
        val coord = coordinator()

        // Open overlay
        val job1 = launch { coord.onLeaderKey() }
        advanceUntilIdle()
        assertThat(coord.state).isEqualTo(CoordinatorState.Open)

        // Cancel via second leader key
        coord.onLeaderKey()
        advanceUntilIdle()
        job1.join()
        assertThat(coord.state).isEqualTo(CoordinatorState.Idle)

        // Reopen
        overlayController.resetDeferred()
        val job2 = launch { coord.onLeaderKey() }
        advanceUntilIdle()
        assertThat(coord.state).isEqualTo(CoordinatorState.Open)
        assertThat(overlayController.awaitSelectionCalls).isEqualTo(2)

        overlayController.completeSelection(OverlaySelection.Cancelled)
        advanceUntilIdle()
        job2.join()
        assertThat(coord.state).isEqualTo(CoordinatorState.Idle)
    }
    @Test
    fun `flow-collected leader keys - second key cancels overlay when launched independently`() = runTest {
        val coord = coordinator()
        val leaderKeys = MutableSharedFlow<Unit>(extraBufferCapacity = 1)

        // Simulate the real collection pattern: each event launches independently
        val collectorJob = launch {
            leaderKeys.collect {
                launch { coord.onLeaderKey() }
            }
        }
        advanceUntilIdle()

        // First leader key opens overlay
        leaderKeys.tryEmit(Unit)
        advanceUntilIdle()
        assertThat(coord.state).isEqualTo(CoordinatorState.Open)

        // Second leader key cancels overlay
        leaderKeys.tryEmit(Unit)
        advanceUntilIdle()
        assertThat(overlayController.cancelSelectionCalls).isEqualTo(1)
        assertThat(coord.state).isEqualTo(CoordinatorState.Idle)

        // No spurious re-open
        assertThat(overlayController.awaitSelectionCalls).isEqualTo(1)

        collectorJob.cancel()
    }

    @Test
    fun `overlay visibility callback fires on open and close`() = runTest {
        val coord = coordinator()

        val job = launch { coord.onLeaderKey() }
        advanceUntilIdle()

        // Overlay opened — callback fired with true
        assertThat(visibilityChanges).containsExactly(true)

        // User cancels — callback fired with false
        overlayController.completeSelection(OverlaySelection.Cancelled)
        advanceUntilIdle()
        job.join()

        assertThat(visibilityChanges).containsExactly(true, false)
    }

    @Test
    fun `overlay visibility callback fires false on toggle-cancel`() = runTest {
        val coord = coordinator()

        val job = launch { coord.onLeaderKey() }
        advanceUntilIdle()
        assertThat(visibilityChanges).containsExactly(true)

        // Second leader key cancels overlay
        coord.onLeaderKey()
        advanceUntilIdle()
        job.join()

        // The finally block ensures false is called even on cancellation
        assertThat(visibilityChanges).containsExactly(true, false)
    }
}

// -- Test fakes --

private val TEST_CONTEXT = ActivationContext(
    gameWindowHandle = null,
    gameTitle = "Path of Exile",
    cursorPosition = ScreenPoint(100, 100),
)

private class FakeFocusManager : FocusManager {
    override fun captureActivationContext(): ActivationContext = TEST_CONTEXT
    override fun stealFocusToOverlay(overlayWindowTitle: String) {}
    override fun returnFocusToGame(context: ActivationContext) {}
    override fun excludeWindowFromCapture(windowTitle: String) {}
    override fun setClickThrough(windowTitle: String, enabled: Boolean) {}
}

private class FakeOverlayController : OverlayController {
    var awaitSelectionCalls = 0
    var cancelSelectionCalls = 0
    private var selectionDeferred = CompletableDeferred<OverlaySelection>()

    override fun start() {}
    override fun overlayWindowTitle(): String = "Test Overlay"

    override suspend fun awaitSelection(
        macros: List<MacroRegistration>,
        context: ActivationContext,
    ): OverlaySelection {
        awaitSelectionCalls++
        return selectionDeferred.await()
    }

    override fun showExecutionStatus(macroName: String) {}
    override fun hideExecutionStatus() {}

    override fun cancelSelection() {
        cancelSelectionCalls++
        selectionDeferred.complete(OverlaySelection.Cancelled)
    }

    fun completeSelection(selection: OverlaySelection) {
        selectionDeferred.complete(selection)
    }

    fun resetDeferred() {
        selectionDeferred = CompletableDeferred()
    }
}

private class FakeMacroRegistry : MacroRegistry {
    val macros = listOf(
        MacroRegistration(
            id = "test-macro",
            name = "Test Macro",
            category = "test",
            description = "A test macro",
            gameFilter = setOf("Path of Exile"),
        )
    )

    override fun allMacros(): List<MacroRegistration> = macros
    override fun macrosFor(context: ActivationContext): List<MacroRegistration> = macros
}

private class FakeMacroRunner : MacroRunner {
    private var runDeferred: CompletableDeferred<Unit>? = null

    override suspend fun run(registration: MacroRegistration, context: ActivationContext) {
        val deferred = CompletableDeferred<Unit>()
        runDeferred = deferred
        deferred.await()
    }

    fun completeCurrentRun() {
        runDeferred?.complete(Unit)
    }
}
