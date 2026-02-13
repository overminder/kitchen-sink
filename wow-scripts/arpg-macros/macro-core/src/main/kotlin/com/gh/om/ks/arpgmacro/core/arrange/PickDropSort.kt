package com.gh.om.ks.arpgmacro.core.arrange

import javax.inject.Inject

interface PickDropSort {
    /**
     * Sort [items] in descending order, and optionally add a gap in the sorted items.
     * @param items A list of slots (nonnull values represent items, null values represent empty slots) to be sorted.
     * The list will always contain an empty slot if [splitAfter] is not null (so the gap is pre-allocated).
     * @param compare Knows how to compare [A]
     * @param splitAfter If present, first [splitAfter] sorted items will have a gap (empty item slot)
     * between it and the rest of sorted items.
     * @return A sequence of clicks on the items, which when executed, will sort the items. If there are
     * multiple ways to sort the items by clicks, this should return the smallest number of clicks (there might
     * still be multiple possible return values in ths case, but that's fine -- as long as the algorithm is
     * deterministic).
     * Example: sortDescAndSplit([1, null, 2], intCompare) = listOf(2, 0, 1).map(::ClickOn)
     * Example: sortDescAndSplit([1, 2, null], intCompare, 1) = listOf(1, 0, 2).map(::ClickOn)
     */
    fun <A> sortDescAndSplit(
        items: List<A?>,
        compare: Comparator<A>,
        splitAfter: Int? = null,
    ) : List<ClickOn>

    /**
     * - When the mouse pointer doesn't hold an item, a click on an item picks it up on the pointer.
     * - When the mouse pointer holds an item, a click on an empty slot will drop the item.
     * - When the mouse pointer holds an item A, a click on another item B will swap the items: A is dropped,
     *   B is picked up.
     * @param ix The index of the slot on the input list of [PickDropSort.sortDescAndSplit]
     */
    data class ClickOn(val ix: Int)
}

class PickDropSortImpl @Inject constructor() : PickDropSort {
    override fun <A> sortDescAndSplit(
        items: List<A?>,
        compare: Comparator<A>,
        splitAfter: Int?,
    ): List<PickDropSort.ClickOn> {
        val target = computeTarget(items, compare, splitAfter)
        val perm = buildPermutation(items, target, compare)
        val cycles = findCycles(perm)
        return generateClicks(cycles, items)
    }

    /**
     * Build the target layout: non-null items sorted descending, packed at the start,
     * with an optional gap at position [splitAfter].
     */
    private fun <A> computeTarget(
        items: List<A?>,
        compare: Comparator<A>,
        splitAfter: Int?,
    ): List<A?> {
        val sorted = items.filterNotNull().sortedWith(compare.reversed())
        val result = MutableList<A?>(items.size) { null }
        var pos = 0
        for (item in sorted) {
            if (splitAfter != null && pos == splitAfter) pos++
            result[pos] = item
            pos++
        }
        return result
    }

    /**
     * Build a permutation where perm[i] = j means "target position i should receive the item
     * currently at source position j". Maximizes fixed points (items already in place) to
     * minimize the number of clicks needed.
     */
    private fun <A> buildPermutation(
        source: List<A?>,
        target: List<A?>,
        compare: Comparator<A>,
    ): IntArray {
        val n = source.size
        val perm = IntArray(n) { it }
        val fixed = BooleanArray(n)

        // Mark fixed points: positions where source already matches target
        for (i in 0 until n) {
            if (matches(source[i], target[i], compare)) {
                fixed[i] = true
            }
        }

        // Collect unfixed source positions, grouped by null vs non-null
        val nullSources = mutableListOf<Int>()
        val itemSources = mutableListOf<Pair<Int, A>>()
        for (i in 0 until n) {
            if (fixed[i]) continue
            val s = source[i]
            if (s == null) nullSources.add(i) else itemSources.add(i to s)
        }

        // Match each unfixed target position to a source position with the same value
        for (i in 0 until n) {
            if (fixed[i]) continue
            val t = target[i]
            if (t == null) {
                perm[i] = nullSources.removeFirst()
            } else {
                val idx = itemSources.indexOfFirst { compare.compare(it.second, t) == 0 }
                perm[i] = itemSources.removeAt(idx).first
            }
        }

        return perm
    }

    private fun <A> matches(a: A?, b: A?, compare: Comparator<A>): Boolean {
        return when {
            a == null && b == null -> true
            a == null || b == null -> false
            else -> compare.compare(a, b) == 0
        }
    }

    /**
     * Decompose the permutation into cycles. Fixed points (perm[i]==i) are skipped.
     */
    private fun findCycles(perm: IntArray): List<List<Int>> {
        val visited = BooleanArray(perm.size)
        val cycles = mutableListOf<List<Int>>()
        for (i in perm.indices) {
            if (visited[i] || perm[i] == i) {
                visited[i] = true
                continue
            }
            val cycle = mutableListOf<Int>()
            var j = i
            while (!visited[j]) {
                visited[j] = true
                cycle.add(j)
                j = perm[j]
            }
            if (cycle.size > 1) {
                cycles.add(cycle)
            }
        }
        return cycles
    }

    /**
     * Generate the click sequence from cycles.
     *
     * For a cycle (c1, c2, ..., ck) where perm[c1]=c2, perm[c2]=c3, ..., perm[ck]=c1:
     *
     * If the cycle contains a null slot at source[cj], rotate so null is first, then
     * emit clicks in reverse order: ck, c(k-1), ..., c1. This takes k clicks.
     *
     * If the cycle has no null, emit: c1, ck, c(k-1), ..., c2, c1. This takes k+1 clicks.
     */
    private fun <A> generateClicks(
        cycles: List<List<Int>>,
        source: List<A?>,
    ): List<PickDropSort.ClickOn> {
        val clicks = mutableListOf<PickDropSort.ClickOn>()
        for (cycle in cycles) {
            val nullIdx = cycle.indexOfFirst { source[it] == null }
            if (nullIdx >= 0) {
                // Rotate so null is at position 0, then emit reversed
                val rotated = cycle.subList(nullIdx, cycle.size) + cycle.subList(0, nullIdx)
                for (i in rotated.size - 1 downTo 0) {
                    clicks.add(PickDropSort.ClickOn(rotated[i]))
                }
            } else {
                // No null: pick up c1, swap through ck..c2, drop at c1
                clicks.add(PickDropSort.ClickOn(cycle[0]))
                for (i in cycle.size - 1 downTo 1) {
                    clicks.add(PickDropSort.ClickOn(cycle[i]))
                }
                clicks.add(PickDropSort.ClickOn(cycle[0]))
            }
        }
        return clicks
    }
}
