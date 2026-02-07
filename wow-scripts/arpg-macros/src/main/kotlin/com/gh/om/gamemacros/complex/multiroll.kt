package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.safeDelayK
import java.awt.Point
import kotlin.time.Duration.Companion.milliseconds

object PoeMultiRoll {
    interface ItemChecker<R: CheckResult> {
        fun evaluate(item: PoeRollableItem): R
        fun generateReport(results: List<R>): String
    }

    data class SimpleResult(override val isGood: Boolean) : CheckResult

    interface CheckResult {
        val isGood: Boolean
    }

    suspend fun <R: CheckResult> rollItems(
        checker: ItemChecker<R>,
        itemsToRoll: List<Point>,
        rerollProvider: RerollProvider,
        shouldContinue: () -> Boolean,
    ) {
        val rolledItems = mutableListOf<PoeRollableItem>()
        var rerollCount = 0
        val mutItemRemaining = itemsToRoll.toMutableList()
        // We'll pop rolled maps from the list
        mutItemRemaining.reverse()

        fun report() {
            val results = rolledItems.map(checker::evaluate)
            val avgCost = (rerollCount.toDouble() / results.size).fmt()
            val lines = listOf(
                "Rolled ${results.size} items in $rerollCount tries. Avg $avgCost tries",
                checker.generateReport(results),
            )
            lines.forEach(::println)
        }

        while (true) {
            if (mutItemRemaining.isEmpty() || !shouldContinue()) {
                break
            }
            val itemSlot = mutItemRemaining.last()
            val item = getItemAt(itemSlot)
            if (checker.evaluate(item).isGood) {
                mutItemRemaining.removeLast()
                rolledItems.add(item)
            } else {
                if (rerollProvider.hasMore()) {
                    rerollCount += 1
                    rerollProvider.applyTo(itemSlot, item)
                } else {
                    // Not enough currency left
                    break
                }
            }
        }

        report()
    }

    /**
     * @return Item at [slot]
     */
    private suspend fun getItemAt(slot: Point): PoeRollableItem {
        MouseHooks.moveTo(slot)
        safeDelayK(30.milliseconds)

        val ad = PoeInteractor.getAdvancedDescriptionOfItemUnderMouse() ?: ""
        return PoeItemParser.parseAsRollable(ad)
    }
}

