package com.gh.om.ks.arpgmacro.core

import kotlin.time.Duration.Companion.milliseconds

/**
 * Result of evaluating a single item.
 */
interface CheckResult {
    val isGood: Boolean
}

/**
 * Evaluates items and generates reports.
 */
interface ItemChecker<R : CheckResult> {
    fun evaluate(item: PoeRollableItem): R
    fun generateReport(results: List<R>): String
}

data class RollReport(
    val itemsRolled: Int,
    val totalRerolls: Int,
    val details: String,
)

/**
 * Core loop that processes a batch of items, evaluating each and rerolling
 * until it meets criteria or resources are exhausted.
 */
class MultiRollLoop(
    private val interactor: PoeInteractor,
    private val mouse: MouseOutput,
    private val clock: Clock,
) {
    /**
     * Roll items at the given screen positions until each passes the checker
     * or currency/cancellation stops the process.
     *
     * @param checker evaluates whether an item is good enough
     * @param itemsToRoll screen positions of items to roll
     * @param rerollProvider applies currency to reroll items
     * @param shouldContinue callback for cancellation support
     * @return report of the rolling session
     */
    suspend fun <R : CheckResult> rollItems(
        checker: ItemChecker<R>,
        itemsToRoll: List<ScreenPoint>,
        rerollProvider: RerollProvider,
        shouldContinue: () -> Boolean,
    ): RollReport {
        val rolledItems = mutableListOf<PoeRollableItem>()
        var rerollCount = 0
        val remaining = itemsToRoll.toMutableList()
        remaining.reverse()

        while (remaining.isNotEmpty() && shouldContinue()) {
            val itemSlot = remaining.last()
            val item = getItemAt(itemSlot)
            if (checker.evaluate(item).isGood) {
                remaining.removeLast()
                rolledItems.add(item)
            } else {
                if (rerollProvider.hasMore()) {
                    rerollCount += 1
                    rerollProvider.applyTo(itemSlot, item)
                } else {
                    break
                }
            }
        }

        val results = rolledItems.map(checker::evaluate)
        val avgCost = if (results.isNotEmpty()) {
            (rerollCount.toDouble() / results.size).fmt()
        } else {
            "N/A"
        }
        val details = "Rolled ${results.size} items in $rerollCount tries. Avg $avgCost tries\n" +
                checker.generateReport(results)

        return RollReport(
            itemsRolled = results.size,
            totalRerolls = rerollCount,
            details = details,
        )
    }

    private suspend fun getItemAt(slot: ScreenPoint): PoeRollableItem {
        mouse.moveTo(slot)
        clock.delay(30.milliseconds)
        val text = interactor.getItemDescriptionAt(slot) ?: ""
        return PoeItemParser.parseAsRollable(text)
    }
}
