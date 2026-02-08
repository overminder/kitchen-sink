package com.gh.om.ks.arpgmacro.core

/**
 * The "runnable" part of a macro. The triggering logic is from the caller.
 */
interface MacroDef {
    /**
     * Gather environmental information to prepare for the macro run.
     */
    suspend fun prepare() : Prepared

    /**
     * A macro that knows how to run.
     */
    fun interface Prepared {
        /**
         * The macro is asked to run (e.g. when its start key sequence is pressed by user).
         * The macro should cooperatively check whether it should continue at safe points (e.g. loop header).
         */
        suspend fun run()
    }
}