package com.gh.om.ks.arpgmacro.app

import com.gh.om.ks.arpgmacro.core.craft.CurrencySlots
import com.gh.om.ks.arpgmacro.core.GlobalMacroConfig
import com.gh.om.ks.arpgmacro.core.ScreenPoint
import javax.inject.Inject

// -- Currency tab slot positions (2560x1440) --

val POE1_CURRENCY_TAB_SLOTS = CurrencySlots(
    transmute = ScreenPoint(62, 355),
    alt = ScreenPoint(146, 361),
    aug = ScreenPoint(302, 432),
    regal = ScreenPoint(574, 352),
    exalt = ScreenPoint(397, 359),
    scour = ScreenPoint(576, 678),
    annul = ScreenPoint(226, 360),
    chaos = ScreenPoint(730, 356),
    alch = ScreenPoint(221, 609),
    armourScrap = ScreenPoint(572, 273),
    whetstone = ScreenPoint(501, 277),
)

class MacroConfigImpl @Inject constructor(): GlobalMacroConfig {
    override val stopKey: String = "F4"
}
