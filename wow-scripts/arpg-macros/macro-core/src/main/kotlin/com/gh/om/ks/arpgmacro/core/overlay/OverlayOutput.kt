package com.gh.om.ks.arpgmacro.core.overlay

/**
 * An entry displayed in the overlay picker.
 */
data class OverlayEntry(
    val key: String,
    val label: String,
    val category: String = "",
)

/**
 * Controls an in-game overlay that shows available macro commands.
 * Implementations must be thread-safe (called from coroutine threads,
 * rendered on UI thread).
 */
interface OverlayOutput {
    /** Start the overlay window. Call once at startup. Default no-op. */
    fun start() {}

    fun show(entries: List<OverlayEntry>)
    fun hide()
}
