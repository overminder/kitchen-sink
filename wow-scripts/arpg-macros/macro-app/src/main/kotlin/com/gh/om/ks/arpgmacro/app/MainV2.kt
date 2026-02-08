package com.gh.om.ks.arpgmacro.app

import com.gh.om.ks.arpgmacro.recipe.TownHotkeyMacro
import com.github.kwhat.jnativehook.GlobalScreen
import kotlinx.coroutines.Job
import kotlinx.coroutines.async
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.runBlocking

fun main() {
    GlobalScreen.registerNativeHook()
    try {
        val component = DaggerAppComponent.create()
        val mdefs = component.macroDefs()
        // This makes it clear which macro is triggered by which key.
        val macroAndKeys = listOf(
            mdefs.printMousePosMacro to "02",
            mdefs.mapRollingMacro to "11",
            mdefs.sortInStashMacro to "14",
            mdefs.craftRollingMacro to "15",
        )
        println("Launching macros (Alt+X leader key, F4 to stop)")
        val jobs = mutableListOf<Job>()
        runBlocking {
            for ((m, keySeq) in macroAndKeys) {
                println("  ${m.javaClass.simpleName}:      Alt+X, $keySeq")
                jobs += async {
                    val prepared = m.prepare()
                    component.leaderKeyDetector().isEnabled(keySeq).collect { enabled ->
                        if (enabled) {
                            prepared.run()
                        }
                    }
                }
            }

            // Town hotkey macros (not leader-key based)
            jobs += async {
                component.macroDefs().townHotkeyMacroFactory.create(
                    windowTitle = "Path of Exile",
                    hotkeys = mapOf(
                        "F5" to "/hideout",
                        "F6" to "/kingsmarch",
                        "F7" to "/heist",
                    ),
                ).run()
            }
            jobs += async {
                component.macroDefs().townHotkeyMacroFactory.create(
                    windowTitle = "Path of Exile 2",
                    hotkeys = mapOf(
                        "F5" to "/hideout",
                    ),
                ).run()
            }

            jobs.joinAll()
        }
    } finally {
        GlobalScreen.unregisterNativeHook()
    }
}
