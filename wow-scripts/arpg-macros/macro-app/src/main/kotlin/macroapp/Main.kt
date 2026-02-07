package macroapp

import com.github.kwhat.jnativehook.GlobalScreen
import kotlinx.coroutines.async
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.runBlocking

fun main() {
    GlobalScreen.registerNativeHook()
    try {
        val component = DaggerAppComponent.create()
        println("Launching macros (Alt+X leader key, F4 to stop)")
        println("  Mouse pos:      Alt+X, 0, 2")
        println("  Map rolling:    Alt+X, 1, 1")
        println("  Sort in stash:  Alt+X, 1, 4")
        println("  Craft rolling:  Alt+X, 1, 5")
        println("  Town hotkeys:   F5=hideout, F6=kingsmarch, F7=heist (POE/POE2)")
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
    } finally {
        GlobalScreen.unregisterNativeHook()
    }
}
