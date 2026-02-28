package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.MouseOutput
import com.gh.om.ks.arpgmacro.core.overlay.ActivationContext
import com.gh.om.ks.arpgmacro.core.println
import javax.inject.Inject
import kotlin.time.Duration.Companion.milliseconds

/**
 * Ctrl+clicks 300 times at the cursor position captured on activation.
 * Ports [ctrlClickManyTimesInPoe].
 *
 * Use case: bulk beast-deletion in the Bestiary UI.
 * The cursor position is read from [ActivationContext.cursorPosition] (captured before the overlay
 * was shown), so the user positions the cursor on the target before triggering the macro.
 */
class CtrlClickAtCursorMacro @Inject constructor(
    private val keyboard: KeyboardOutput,
    private val mouseOut: MouseOutput,
    private val clock: Clock,
    private val shouldContinueChecker: ShouldContinueChecker,
    private val consoleOutput: ConsoleOutput,
) : MacroDef {
    override suspend fun prepare(): MacroDef.Prepared {
        val shouldContinue = shouldContinueChecker.get(anyWindowTitles = GameTitles.ALL_POE)
        return MacroDef.Prepared { context ->
            if (!shouldContinue.value) return@Prepared
            val cursorPos = context.cursorPosition
            consoleOutput.println("Ctrl-clicking at (${cursorPos.x}, ${cursorPos.y})")
            repeat(300) {
                if (!shouldContinue.value) return@Prepared
                keyboard.postPress("Ctrl")
                clock.delay(50.milliseconds)
                mouseOut.postClick(cursorPos)
                clock.delay(50.milliseconds)
                keyboard.postRelease("Ctrl")
                clock.delay(100.milliseconds)
            }
        }
    }
}
