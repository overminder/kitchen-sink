package com.gh.om.ks.arpgmacro.core.craft

import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.item.PoeCurrency
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.item.PoeItemParser
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem
import com.gh.om.ks.arpgmacro.core.ScreenPoint
import javax.inject.Inject

/**
 * Screen positions for each currency type in the currency stash tab.
 */
data class CurrencySlots(
    val transmute: ScreenPoint,
    val alt: ScreenPoint,
    val aug: ScreenPoint,
    val regal: ScreenPoint,
    val exalt: ScreenPoint,
    val scour: ScreenPoint,
    val annul: ScreenPoint,
    val chaos: ScreenPoint,
    val alch: ScreenPoint,
    val armourScrap: ScreenPoint,
    val whetstone: ScreenPoint,
)

interface CurrencySlotsV2 {
    fun at(type: PoeCurrency.KnownType): ScreenPoint
}

/**
 * A [RerollProvider] that uses [CraftMethods] + [CraftDecisionMaker] to
 * reroll items via alt/aug/regal crafting.
 *
 * Replaces the old CrafterAsRerollProvider + BaseRelocatableCrafter stack
 * by delegating currency application to [com.gh.om.ks.arpgmacro.core.PoeInteractor.applyCurrencyTo].
 */
class CraftRerollProvider(
    private var fuel: Int = 100,
    private val dm: CraftDecisionMaker,
    private val interactor: PoeInteractor,
    private val currencySlots: CurrencySlots,
    private val clock: Clock,
    private val craftMethod: suspend (
        PoeItemCrafter,
        CraftDecisionMaker,
    ) -> CraftDecisionMaker.Decision = CraftMethods::altAugRegalExaltOnce,
) : RerollProvider {

    override suspend fun hasMore(): Boolean {
        return fuel > 0
    }

    override suspend fun applyTo(itemSlot: ScreenPoint, item: PoeRollableItem) {
        val crafter = InteractorBackedCrafter(itemSlot, item)
        fuel -= 1
        craftMethod(crafter, dm)
    }

    /**
     * [PoeItemCrafter] backed by [PoeInteractor]. Each currency call
     * right-clicks the currency slot and left-clicks the item slot.
     */
    private inner class InteractorBackedCrafter(
        private val itemSlot: ScreenPoint,
        initialItem: PoeRollableItem,
    ) : PoeItemCrafter {
        private var cachedItem: PoeRollableItem? = initialItem

        override suspend fun getCurrentItem(): PoeRollableItem {
            cachedItem?.let { return it }
            val text = interactor.getItemDescriptionAt(itemSlot) ?: ""
            val parsed = PoeItemParser.parseAsRollable(text)
            cachedItem = parsed
            return parsed
        }

        private suspend fun useCurrency(slot: ScreenPoint) {
            cachedItem = null
            interactor.applyCurrencyTo(slot, itemSlot)
        }

        override suspend fun transmute() = useCurrency(currencySlots.transmute)
        override suspend fun alternate() = useCurrency(currencySlots.alt)
        override suspend fun augment() = useCurrency(currencySlots.aug)
        override suspend fun regal() = useCurrency(currencySlots.regal)
        override suspend fun exalt() = useCurrency(currencySlots.exalt)
        override suspend fun scour() = useCurrency(currencySlots.scour)
        override suspend fun annul() = useCurrency(currencySlots.annul)
        override suspend fun chaos() = useCurrency(currencySlots.chaos)
        override suspend fun alch() = useCurrency(currencySlots.alch)
        override suspend fun armourerScrap() = useCurrency(currencySlots.armourScrap)
        override suspend fun whetstone() = useCurrency(currencySlots.whetstone)
    }
}

class CraftRerollProviderV2(
    private var fuel: Int = 100,
    private val dm: CraftDecisionMakerV2,
    private val deps: Deps,
) : RerollProvider {
    private val currencyCount = mutableMapOf<PoeCurrency.KnownType, Int>()
    private var ranOutOfCurrencyForItemSlot: ScreenPoint? = null

    override suspend fun hasMore(): Boolean {
        return fuel > 0 && ranOutOfCurrencyForItemSlot == null
    }

    override suspend fun applyTo(
        itemSlot: ScreenPoint,
        item: PoeRollableItem
    ) {
        require(fuel > 0)

        if (ranOutOfCurrencyForItemSlot != null && itemSlot != ranOutOfCurrencyForItemSlot) {
            // Clear previously remembered hasMore check
            ranOutOfCurrencyForItemSlot = null
        }

        val d = dm.getDecision(item)
        val currency = d.type
        require(currency != null && !d.isGood) {
            "Should not call applyTo when item is already good"
        }

        val count = getOrFindCurrencyCount(currency)
        if (count <= 0) {
            // Remember that we can't proceed in next hasMore check
            ranOutOfCurrencyForItemSlot = itemSlot
        } else {
            fuel -= 1
            deps.interactor.applyCurrencyTo(
                deps.currencySlots.at(currency),
                itemSlot
            )
            currencyCount[currency] = count - 1
        }
    }

    private suspend fun getOrFindCurrencyCount(currency: PoeCurrency.KnownType): Int {
        currencyCount[currency]?.let {
            return it
        }
        val currencySlot = deps.currencySlots.at(currency)
        val freshCount = deps.interactor.getCurrencyCountAt(
            currencySlot,
            listOf(currency)
        )
        currencyCount[currency] = freshCount
        return freshCount
    }

    class Deps @Inject constructor(
        val interactor: PoeInteractor,
        val currencySlots: CurrencySlotsV2,
    )

    class Factory @Inject constructor(private val deps: Deps) {
        fun create(fuel: Int, dm: CraftDecisionMakerV2) = CraftRerollProviderV2(fuel, dm, deps)
    }
}
