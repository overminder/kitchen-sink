package macrocore

import kotlin.time.Duration.Companion.milliseconds

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

/**
 * A [RerollProvider] that uses [CraftMethods] + [CraftDecisionMaker] to
 * reroll items via alt/aug/regal crafting.
 *
 * Replaces the old CrafterAsRerollProvider + BaseRelocatableCrafter stack
 * by delegating currency application to [PoeInteractor.applyCurrencyTo].
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
