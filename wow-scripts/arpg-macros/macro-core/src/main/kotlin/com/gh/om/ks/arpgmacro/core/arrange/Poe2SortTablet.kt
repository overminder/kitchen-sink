package com.gh.om.ks.arpgmacro.core.arrange

import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.MouseOutput
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.item.PoeItem
import com.gh.om.ks.arpgmacro.core.map.fmt
import com.gh.om.ks.arpgmacro.core.parseItemAt
import com.gh.om.ks.arpgmacro.di.GameType
import javax.inject.Inject
import kotlin.math.max
import kotlin.time.Duration.Companion.milliseconds

class Poe2SortTablet(
    private val deps: Deps,
    private val scorer: (PoeItem) -> Double,
) {
    suspend fun sortInBag(shouldContinue: () -> Boolean) {
        if (!shouldContinue()) {
            return
        }

        val slots = deps.interactor.getOccupiedBagSlots(includeEmptySlotAfter = true)
        println("SortTablet, slots: $slots")
        val occupied = slots.take(slots.size - 1)
        val scores = occupied.mapTo(mutableListOf()) {
            deps.interactor.parseItemAt(it)?.let(scorer)
        }
        // For the empty slot.
        scores += null
        println("SortTablet, scores: ${scores.map(Number?::fmt)}")
        val actions = deps.pickDropSort.sortDescAndSplit(
            scores,
            Comparator.naturalOrder(),
            // Split to highlight positive scores
            splitAfter = scores.count { (it ?: 0.0) > 0 },
        )
        println("SortTablet, actions: $actions")
        for (action in actions) {
            if (!shouldContinue()) {
                return
            }
            val point = slots[action.ix]
            deps.clock.delay(100.milliseconds)
            deps.mouseOut.moveTo(point)
            deps.clock.delay(100.milliseconds)
            deps.mouseOut.postClick(point)
        }
    }

    class Deps @Inject constructor(
        val pickDropSort: PickDropSort,
        val gameType: GameType,
        val interactor: PoeInteractor,
        val mouseOut: MouseOutput,
        val clock: Clock,
    )

    class Factory @Inject constructor(private val deps: Deps) {
        fun create(
            scorer: (PoeItem) -> Double
        ) = Poe2SortTablet(deps, scorer)
    }
}
