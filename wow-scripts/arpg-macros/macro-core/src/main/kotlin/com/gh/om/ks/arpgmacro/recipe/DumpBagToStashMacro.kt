package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.overlay.ActivationContext
import com.gh.om.ks.arpgmacro.core.println
import javax.inject.Inject

/**
 * Ctrl+click (or Ctrl+Shift+click if [forced]) all occupied bag slots to stash.
 * Ports [PoeDumpBag::bagToStash] and [PoeDumpBag::bagToStashForced].
 */
class DumpBagToStashMacro(
    private val poeInteractor: PoeInteractor,
    private val shouldContinueChecker: ShouldContinueChecker,
    private val consoleOutput: ConsoleOutput,
    private val forced: Boolean,
) : MacroDef {
    override suspend fun prepare(): MacroDef.Prepared {
        val shouldContinue = shouldContinueChecker.get(anyWindowTitles = GameTitles.ALL_POE)
        return MacroDef.Prepared { _ ->
            if (!shouldContinue.value) return@Prepared
            val slots = poeInteractor.getOccupiedBagSlots()
            if (slots.isEmpty()) {
                consoleOutput.println("No items found in bag")
                return@Prepared
            }
            consoleOutput.println("${if (forced) "Force-dumping" else "Dumping"} ${slots.size} items to stash")
            for (slot in slots) {
                if (!shouldContinue.value) break
                if (forced) {
                    poeInteractor.forceSendItemToCurrentStash(slot)
                } else {
                    poeInteractor.sendItemToOtherSide(slot)
                }
            }
        }
    }

    class Factory @Inject constructor(
        private val poeInteractor: PoeInteractor,
        private val shouldContinueChecker: ShouldContinueChecker,
        private val consoleOutput: ConsoleOutput,
    ) {
        fun create(forced: Boolean) =
            DumpBagToStashMacro(poeInteractor, shouldContinueChecker, consoleOutput, forced)
    }
}
