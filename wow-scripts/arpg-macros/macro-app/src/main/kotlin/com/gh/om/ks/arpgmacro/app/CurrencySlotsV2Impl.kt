package com.gh.om.ks.arpgmacro.app

import com.gh.om.ks.arpgmacro.core.craft.CurrencySlotsV2
import com.gh.om.ks.arpgmacro.core.item.PoeCurrency
import com.gh.om.ks.arpgmacro.core.ScreenPoint
import com.gh.om.ks.arpgmacro.core.offset
import com.gh.om.ks.arpgmacro.di.GameScope
import com.gh.om.ks.arpgmacro.di.GameType
import javax.inject.Inject

@GameScope
class CurrencySlotsV2Impl @Inject constructor(
    private val gameType: GameType,
) : CurrencySlotsV2 {
    override fun at(type: PoeCurrency.KnownType): ScreenPoint {
        return when (gameType) {
            GameType.POE1 -> getForPoe(type)
            GameType.POE2 -> getForPoe2(type)
            GameType.Diablo3,
            GameType.Diablo4 -> error("$gameType doesn't have currency")
        }
    }

    private fun getForPoe(type: PoeCurrency.KnownType): ScreenPoint {
        val currencySlots = POE1_CURRENCY_TAB_SLOTS
        return when (type) {
            PoeCurrency.Simple.Scour ->
                currencySlots.scour
            PoeCurrency.Simple.Alch ->
                currencySlots.alch
            PoeCurrency.Simple.Binding ->
                TODO("Binding not yet located")
            PoeCurrency.Simple.Annul ->
                currencySlots.annul
            is PoeCurrency.TieredType -> {
                require(type.tier == null) {
                    "POE1 doesn't have tiered ${type.kind.repr}"
                }
                when (type.kind) {
                    PoeCurrency.CanHaveTier.Trans ->
                        currencySlots.transmute
                    PoeCurrency.CanHaveTier.Aug ->
                        currencySlots.aug
                    PoeCurrency.CanHaveTier.Regal ->
                        currencySlots.regal
                    PoeCurrency.CanHaveTier.Exalt ->
                        currencySlots.exalt
                    PoeCurrency.CanHaveTier.Chaos ->
                        currencySlots.chaos
                }
            }
        }
    }

    private fun getForPoe2(type: PoeCurrency.KnownType): ScreenPoint {
        return when (type) {
            PoeCurrency.Simple.Alch ->
                ScreenPoint(351, 237)
            PoeCurrency.Simple.Annul ->
                ScreenPoint(533, 238)
            is PoeCurrency.TieredType -> {
                val origin = when (type.kind) {
                    PoeCurrency.CanHaveTier.Trans ->
                        ScreenPoint(86, 236)
                    PoeCurrency.CanHaveTier.Aug ->
                        ScreenPoint(81, 334)
                    PoeCurrency.CanHaveTier.Regal ->
                        ScreenPoint(80, 422)
                    PoeCurrency.CanHaveTier.Exalt ->
                        ScreenPoint(83, 510)
                    PoeCurrency.CanHaveTier.Chaos ->
                        ScreenPoint(84, 600)
                }
                getTiered(origin, type.tier)
            }
            else ->
                error("Not implemented: $type (or maybe POE2 doesn't have that)")
        }
    }

    private fun getTiered(origin: ScreenPoint, tier: PoeCurrency.Tier?): ScreenPoint {
        return when (tier) {
            null -> origin
            PoeCurrency.Tier.Greater -> origin.offset(82, 1)
            PoeCurrency.Tier.Perfect -> origin.offset(82 * 2, -1)
        }
    }
}
