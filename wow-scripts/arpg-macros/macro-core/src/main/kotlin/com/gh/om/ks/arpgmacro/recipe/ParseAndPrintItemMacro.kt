package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.MacroDef
import com.gh.om.ks.arpgmacro.core.MouseInput
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.item.PoeItemParser
import com.gh.om.ks.arpgmacro.core.println
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.stateIn
import javax.inject.Inject

class ParseAndPrintItemMacro @Inject constructor(
    private val shouldContinueChecker: ShouldContinueChecker,
    private val mouseInput: MouseInput,
    private val poeInteractor: PoeInteractor,
    private val consoleOutput: ConsoleOutput,
) : MacroDef {
    override suspend fun prepare(): MacroDef.Prepared {
        val mousePosition = mouseInput.motionEvents()
            .stateIn(CoroutineScope(currentCoroutineContext()))
        val shouldContinue = shouldContinueChecker.get(GameTitles.ALL_POE)
        return MacroDef.Prepared {
            if (!shouldContinue.value) {
                return@Prepared
            }

            val pos = mousePosition.value
            val ad = poeInteractor.getItemDescriptionAt(pos).orEmpty()
            val item = PoeItemParser.parse(ad)
            consoleOutput.println(item.toString())
        }
    }
}