package com.gh.om.ks.arpgmacro.core

import com.gh.om.ks.arpgmacro.core.overlay.BgMacroEventSink

class ReportingKeyboardOutput(
    private val macroName: String,
    private val delegate: KeyboardOutput,
    private val sink: BgMacroEventSink,
    private val isSuppressed: () -> Boolean = { false },
) : KeyboardOutput by delegate {
    override fun postPress(keyCode: String) {
        if (isSuppressed()) return
        delegate.postPress(keyCode)
        sink.onKeyPress(macroName, keyCode)
    }

    override fun postRelease(keyCode: String) {
        if (isSuppressed()) return
        delegate.postRelease(keyCode)
    }
}
