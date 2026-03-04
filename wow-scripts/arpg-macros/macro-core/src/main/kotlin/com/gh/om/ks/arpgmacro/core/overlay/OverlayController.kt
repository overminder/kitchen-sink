package com.gh.om.ks.arpgmacro.core.overlay

import kotlinx.coroutines.flow.StateFlow

/**
 * Result of the user interacting with the overlay.
 */
sealed class OverlaySelection {
    /** User selected a macro to run. */
    data class Selected(val registration: MacroRegistration) : OverlaySelection()
    /** User cancelled (Escape, click outside, or timeout). */
    data object Cancelled : OverlaySelection()
}

/**
 * Interactive overlay that the user can select macros from.
 * Replaces the passive [OverlayOutput] from v2.
 *
 * The overlay is a focused, interactive window. The coordinator calls [awaitSelection]
 * which shows the window, waits for the user to pick a macro or cancel, then returns.
 */
interface OverlayController {
    /** Start the overlay window system. Call once at startup. */
    fun start()

    /** The window title, used by [FocusManager] to find the native window handle. */
    fun overlayWindowTitle(): String

    /**
     * Show the overlay with the given macros, wait for user selection or cancellation.
     * The overlay steals visual focus and becomes interactive.
     * Returns when the user selects a macro, cancels, or the inactivity timeout fires.
     */
    suspend fun awaitSelection(
        macros: List<MacroRegistration>,
        context: ActivationContext,
    ): OverlaySelection

    /**
     * Show a non-interactive (click-through) status indicator while [macroName] runs.
     * Call before [MacroRunner.run]; the overlay window remains visible but non-focusable.
     */
    fun showExecutionStatus(macroName: String)

    /** Hide the execution status indicator. Call when the macro completes or is cancelled. */
    fun hideExecutionStatus()

    /**
     * Connect background macro state to the overlay so it can show a persistent toggle badge.
     * The badge is visible whenever the overlay is not showing the macro picker.
     * Default no-op for implementations that don't support the badge.
     */
    fun connectBackgroundMacros(isEnabled: StateFlow<Boolean>, onToggle: () -> Unit) = Unit
}
