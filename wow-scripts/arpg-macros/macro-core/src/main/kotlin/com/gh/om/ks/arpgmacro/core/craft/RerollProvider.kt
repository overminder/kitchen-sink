package com.gh.om.ks.arpgmacro.core.craft

import com.gh.om.ks.arpgmacro.core.item.PoeCurrency
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.item.PoeItem
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem
import com.gh.om.ks.arpgmacro.core.ScreenPoint
import com.gh.om.ks.arpgmacro.core.item.isMapLike

/**
 * Provides currency reroll capability. Tracks remaining currency and
 * applies appropriate rerolling strategy based on item rarity.
 *
 * This can be stateful -- each reroll session will instantiate a fresh instance.
 */
interface RerollProvider {
    suspend fun hasMore(): Boolean
    suspend fun applyTo(itemSlot: ScreenPoint, item: PoeRollableItem)
}

/**
 * Rerolls using Chaos Orbs. Suitable for re-rolling rare maps.
 */
class ChaosRerollProvider(
    private val fuel: Int = 100,
    private val interactor: PoeInteractor,
    private val chaosSlot: ScreenPoint,
    private val scourSlot: ScreenPoint,
    private val alchSlot: ScreenPoint,
    private val chaosType: PoeCurrency.KnownType = PoeCurrency.Companion.Chaos,
) : RerollProvider {
    private var cachedChaosCount: Int? = null
    private var useCount = 0

    private suspend fun getChaosCount(): Int {
        cachedChaosCount?.let { return it }
        val count = interactor.getCurrencyCountAt(chaosSlot, listOf(chaosType))
        cachedChaosCount = count
        return count
    }

    override suspend fun hasMore(): Boolean {
        return fuel > useCount && getChaosCount() > useCount
    }

    override suspend fun applyTo(itemSlot: ScreenPoint, item: PoeRollableItem) {
        require(hasMore())
        useCount += 1
        when (item.rarity) {
            PoeRollableItem.Rarity.Magic -> {
                interactor.applyCurrencyTo(scourSlot, itemSlot)
                interactor.applyCurrencyTo(alchSlot, itemSlot)
            }
            PoeRollableItem.Rarity.Normal -> {
                interactor.applyCurrencyTo(alchSlot, itemSlot)
            }
            PoeRollableItem.Rarity.Rare -> {
                interactor.applyCurrencyTo(chaosSlot, itemSlot)
            }
            PoeRollableItem.Rarity.Unique -> {
                error("Can't roll unique")
            }
        }
    }
}

/**
 * Rerolls using Scour + Alchemy. Strips the item to normal, then makes it rare.
 */
class ScourAlchRerollProvider(
    private val fuel: Int = 100,
    private val interactor: PoeInteractor,
    private val scourSlot: ScreenPoint,
    private val alchSlot: ScreenPoint,
) : RerollProvider {
    private var cachedMinCount: Int? = null
    private var useCount = 0

    private suspend fun getMinCount(): Int {
        cachedMinCount?.let { return it }
        val scourCount = interactor.getCurrencyCountAt(
            scourSlot, listOf(PoeCurrency.Simple.Scour)
        )
        val alcCount = interactor.getCurrencyCountAt(
            alchSlot, listOf(PoeCurrency.Simple.Alch, PoeCurrency.Simple.Binding)
        )
        val res = minOf(scourCount, alcCount)
        cachedMinCount = res
        return res
    }

    override suspend fun hasMore(): Boolean {
        return fuel > useCount && getMinCount() > useCount
    }

    override suspend fun applyTo(itemSlot: ScreenPoint, item: PoeRollableItem) {
        require(hasMore())
        useCount += 1
        if (item.rarity != PoeRollableItem.Rarity.Normal) {
            interactor.applyCurrencyTo(scourSlot, itemSlot)
        }
        interactor.applyCurrencyTo(alchSlot, itemSlot)
    }
}

/**
 * Uses chaos for T17 maps and scour+alch for everything else.
 */
class ChaosOrAlchMapRerollProvider(
    private val chaos: ChaosRerollProvider,
    private val alch: ScourAlchRerollProvider,
) : RerollProvider {
    override suspend fun hasMore(): Boolean {
        return alch.hasMore() && chaos.hasMore()
    }

    override suspend fun applyTo(itemSlot: ScreenPoint, item: PoeRollableItem) {
        require(item.klass.isMapLike())
        val provider = if (item.klass == PoeItem.Map(PoeItem.MapTier.T17)) {
            chaos
        } else {
            alch
        }
        provider.applyTo(itemSlot, item)
    }
}
