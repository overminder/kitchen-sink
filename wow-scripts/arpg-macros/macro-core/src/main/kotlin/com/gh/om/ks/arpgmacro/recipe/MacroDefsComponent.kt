package com.gh.om.ks.arpgmacro.recipe

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

    val townHotkeyMacro: TownHotkeyMacroV2
)
