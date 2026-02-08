package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.MouseInput
import com.gh.om.ks.arpgmacro.core.Screen
import com.gh.om.ks.arpgmacro.core.println
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.stateIn
import javax.inject.Inject
import kotlin.time.Duration.Companion.seconds

class PrintMousePosMacro @Inject constructor(
    private val mouseInput: MouseInput,
    private val screen: Screen,
    private val clock: Clock,
    private val shouldContinueChecker: ShouldContinueChecker,
    private val consoleOutput: ConsoleOutput,
): MacroDef {
    override suspend fun prepare(): MacroDef.Prepared {
        val mousePosition = mouseInput.motionEvents()
            .stateIn(CoroutineScope(currentCoroutineContext()))

        val shouldContinue = shouldContinueChecker.get(
            anyWindowTitles = GameTitles.ALL_POE,
        )

        return MacroDef.Prepared {
            if (!shouldContinue.value) return@Prepared
            val pos = mousePosition.value
            val color = screen.getPixelColor(pos)
            consoleOutput.println("Mouse(x = ${pos.x}, y = ${pos.y}), color = $color")
            clock.delay(1.seconds)
        }
    }
}