package com.gh.om.ks.arpgmacro.app

import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import javax.inject.Inject

class KotlinConsole @Inject constructor(): ConsoleOutput {
    override fun print(text: String) {
        kotlin.io.print(text)
    }
}