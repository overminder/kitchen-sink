package com.gh.om.ks.arpgmacro.app

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
            mdefs.printMousePosMacro to "02"
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
            jobs.joinAll()
        }
        /*
        runBlocking {
            val jobs = listOf(
                async { printMousePosMacro(component) },
                async { mapRollingMacro(component) },
                async { sortInStashMacro(component) },
                async { craftRollingMacro(component) },
                async {
                    townHotkeyMacro(component, "Path of Exile", mapOf(
                        "F5" to "/hideout",
                        "F6" to "/kingsmarch",
                        "F7" to "/heist",
                    ))
                },
                async {
                    townHotkeyMacro(component, "Path of Exile 2", mapOf(
                        "F5" to "/hideout",
                    ))
                },
            )
            jobs.joinAll()
        }
         */
    } finally {
        GlobalScreen.unregisterNativeHook()
    }
}
