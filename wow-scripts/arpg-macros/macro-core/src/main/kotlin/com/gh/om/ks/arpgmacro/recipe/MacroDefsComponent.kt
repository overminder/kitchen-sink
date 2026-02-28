package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.MacroDef
import javax.inject.Inject

/**
 * A list of all the macros
 */
class MacroDefsComponent @Inject constructor(
    val printMousePos: PrintMousePosMacro,
    val mapRolling: MapRollingMacro,
    val craftRolling: CraftRollingMacro,
    val craftRollingV2: CraftRollingMacroV2,
    val sortInStash: SortInStashMacro,
    val parseAndPrintItem: ParseAndPrintItemMacro,
    val tabletRollingMacro: TabletRollingMacro,

    val townHotkeyMacro: TownHotkeyMacroV2,

    private val dumpBagFactory: DumpBagToStashMacro.Factory,
    val ctrlClickAtCursor: CtrlClickAtCursorMacro,
) {
    val dumpBagToStash: MacroDef get() = dumpBagFactory.create(forced = false)
    val dumpBagToStashForced: MacroDef get() = dumpBagFactory.create(forced = true)
}
