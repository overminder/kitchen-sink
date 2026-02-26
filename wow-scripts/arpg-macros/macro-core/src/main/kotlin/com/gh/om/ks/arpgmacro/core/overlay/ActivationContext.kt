package com.gh.om.ks.arpgmacro.core.overlay

import com.gh.om.ks.arpgmacro.core.ScreenPoint

/**
 * Snapshot of the environment at the moment the leader key is pressed.
 * Captured before stealing focus so we can filter macros and return focus reliably.
 *
 * [gameWindowHandle] is opaque — the platform-specific focus manager knows how to use it.
 */
data class ActivationContext(
    val gameWindowHandle: Any?,
    val gameTitle: String,
    val cursorPosition: ScreenPoint,
)
