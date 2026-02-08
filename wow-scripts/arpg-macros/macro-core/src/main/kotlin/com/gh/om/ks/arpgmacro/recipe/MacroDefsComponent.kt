package com.gh.om.ks.arpgmacro.recipe

import javax.inject.Inject

/**
 * A list of all the macros
 */
class MacroDefsComponent @Inject constructor(
    val printMousePosMacro: PrintMousePosMacro,
    val mapRollingMacro: MapRollingMacro,
    val craftRollingMacro: CraftRollingMacro,
    val sortInStashMacro: SortInStashMacro,
    val townHotkeyMacroFactory: TownHotkeyMacro.Factory,
)
