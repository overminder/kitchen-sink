package com.gh.om.ks.arpgmacro.recipe

import javax.inject.Inject

/**
 * A list of all the macros
 */
class MacroDefsComponent @Inject constructor(
    val printMousePos: PrintMousePosMacro,
    val mapRolling: MapRollingMacro,
    val craftRolling: CraftRollingMacro,
    val sortInStash: SortInStashMacro,
    val parseAndPrintItem: ParseAndPrintItemMacro,

    val townHotkeyMacro: TownHotkeyMacroV2
)
