package com.gh.om.ks.arpgmacro.core.overlay

/**
 * Source of truth for available macros. The overlay reads from this
 * to render the macro list.
 */
interface MacroRegistry {
    /** All registered macros. */
    fun allMacros(): List<MacroRegistration>

    /** Macros applicable to the given activation context (filtered by game title, etc.). */
    fun macrosFor(context: ActivationContext): List<MacroRegistration>
}

/**
 * Runs a selected macro. The coordinator calls this after the user confirms selection.
 */
interface MacroRunner {
    /** Run the macro identified by [registration] in the given [context]. Suspends until complete. */
    suspend fun run(registration: MacroRegistration, context: ActivationContext)
}
