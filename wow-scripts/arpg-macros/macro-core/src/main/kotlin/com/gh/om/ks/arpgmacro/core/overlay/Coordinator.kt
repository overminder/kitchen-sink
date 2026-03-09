package com.gh.om.ks.arpgmacro.core.overlay

import kotlinx.coroutines.delay
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock

/**
 * Coordinator state: the overlay interaction is a linear sequence,
 * so we only need three states.
 */
enum class CoordinatorState {
    /** Overlay hidden, listening for leader key. */
    Idle,
    /** Overlay visible and focused, user is selecting a macro. */
    Open,
    /** A macro is currently executing. */
    MacroRunning,
}

/**
 * Sequences the overlay interaction flow:
 * leader key → capture context → steal focus → await selection → return focus → run macro.
 *
 * The coordinator coroutine is occupied for the full duration (overlay interaction + macro execution).
 * The [state] guard prevents re-entrancy: [onLeaderKey] is a no-op when not [CoordinatorState.Idle].
 */
class Coordinator(
    private val focusManager: FocusManager,
    private val overlayController: OverlayController,
    private val macroRegistry: MacroRegistry,
    private val macroRunner: MacroRunner,
    private val onOverlayVisibilityChanged: (visible: Boolean) -> Unit = {},
) {
    @Volatile
    var state: CoordinatorState = CoordinatorState.Idle
        private set

    private val mutex = Mutex()

    /**
     * Called when the leader key (Alt+X) is detected.
     * No-op if not in Idle state.
     */
    suspend fun onLeaderKey() {
        // Fast path: skip if macro is running
        if (state == CoordinatorState.MacroRunning) return

        // Toggle: cancel overlay if it's open (no lock needed — cancelSelection is thread-safe)
        if (state == CoordinatorState.Open) {
            overlayController.cancelSelection()
            return
        }

        // Serialize to prevent races between rapid Alt+X presses
        mutex.withLock {
            if (state != CoordinatorState.Idle) return

            val context = focusManager.captureActivationContext() ?: return
            val macros = macroRegistry.macrosFor(context)
            if (macros.isEmpty()) return   // not in a recognized game, skip silently

            state = CoordinatorState.Open
            onOverlayVisibilityChanged(true)

            try {
                val selection = overlayController.awaitSelection(macros, context)

                // Always return focus before running macro or on cancel
                focusManager.returnFocusToGame(context)
                // Give the game time to restore input handling after focus switch.
                // Without this, POE1 may ignore injected mouse/key events.
                // The old code (PoeDumpBag::bagToStash) never had this problem because it used leader-key
                // detection via global hooks — the game never lost focus.
                delay(500)

                when (selection) {
                    is OverlaySelection.Cancelled -> {}
                    is OverlaySelection.Selected -> {
                        state = CoordinatorState.MacroRunning
                        overlayController.showExecutionStatus(selection.registration.name)
                        try {
                            macroRunner.run(selection.registration, context)
                        } finally {
                            overlayController.hideExecutionStatus()
                        }
                    }
                }
            } finally {
                onOverlayVisibilityChanged(false)
                state = CoordinatorState.Idle
            }
        }
    }
}
