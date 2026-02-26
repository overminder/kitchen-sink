package com.gh.om.ks.arpgmacro.core.overlay

/**
 * Manages focus stealing/returning between the game window and the overlay.
 * Platform-specific implementations use native APIs (e.g. Win32 SetForegroundWindow).
 */
interface FocusManager {
    /**
     * Capture the current activation context: foreground window handle, title, cursor pos.
     * Call before stealing focus.
     */
    fun captureActivationContext(): ActivationContext?

    /**
     * Steal focus from the game to the overlay window.
     * @param overlayWindowTitle the overlay's window title (used to find the native handle)
     */
    fun stealFocusToOverlay(overlayWindowTitle: String)

    /**
     * Return focus to the game window captured in the activation context.
     */
    fun returnFocusToGame(context: ActivationContext)
}
