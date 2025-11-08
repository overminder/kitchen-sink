package org.example.com.gh.om.gamemacros

import com.gh.om.gamemacros.GameSpecific
import com.github.kwhat.jnativehook.GlobalScreen
import kotlinx.coroutines.async
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.runBlocking

private fun innerMain() {
    println("Launching ${GameSpecific.ALL.size} GameSpecific macros")
    runBlocking {
        val tasks = GameSpecific.ALL.map { mkTask ->
            async { mkTask() }
        }
        tasks.joinAll()
    }
}

fun main() {
    GlobalScreen.registerNativeHook()
    try {
        innerMain()
    } finally {
        // NativeHook will create non-daemon thread when key listeners are added.
        // Stop the thread by unregistering the hook.
        GlobalScreen.unregisterNativeHook()
    }
}
