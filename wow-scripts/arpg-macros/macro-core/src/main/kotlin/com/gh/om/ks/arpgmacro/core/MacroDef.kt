package com.gh.om.ks.arpgmacro.core

import com.gh.om.ks.arpgmacro.core.overlay.ActivationContext

/**
 * The "runnable" part of a macro. The triggering logic is from the caller.
 */
interface MacroDef {
    /**
     * Gather environmental information to prepare for the macro run.
     * Note(lifecycle): This is expected to be called exactly once (per process lifecycle) during application startup.
     */
    suspend fun prepare(): Prepared

    /**
     * A macro that knows how to run.
     */
    fun interface Prepared {
        /**
         * The macro is asked to run (e.g. when its start key sequence is pressed by user).
         * [context] is the activation snapshot (game window, cursor position) captured when the
         * leader key was pressed. Macros that need the original cursor position should read it here.
         * The macro should cooperatively check whether it should continue at safe points (e.g. loop header).
         */
        suspend fun run(context: ActivationContext)
    }
}
