package com.gh.om.ks.arpgmacro.core

import com.gh.om.ks.arpgmacro.core.overlay.BgMacroEventSink

class ReportingKeyboardOutput(
    private val macroName: String,
    private val delegate: KeyboardOutput,
    private val sink: BgMacroEventSink,
) : KeyboardOutput by delegate {
    override fun postPress(keyCode: String) {
        delegate.postPress(keyCode)
        sink.onKeyPress(macroName, keyCode)
    }
}
