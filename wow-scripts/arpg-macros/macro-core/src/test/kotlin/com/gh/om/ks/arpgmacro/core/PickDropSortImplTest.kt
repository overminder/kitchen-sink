package com.gh.om.ks.arpgmacro.core

import com.gh.om.ks.arpgmacro.core.arrange.PickDropSort
import com.gh.om.ks.arpgmacro.core.arrange.PickDropSortImpl
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class PickDropSortImplTest {
    private val sort = PickDropSortImpl()
    private val intCompare = Comparator.naturalOrder<Int>()

    // -- Simulation helper --

    /**
     * Simulate the click sequence on [initial] and return the final slot state.
     * Validates that every click is legal (no picking from empty with empty hand).
     */
    private fun <A> simulate(initial: List<A?>, clicks: List<PickDropSort.ClickOn>): List<A?> {
        val slots = initial.toMutableList()
        var hand: A? = null
        var handFull = false
        for (click in clicks) {
            val ix = click.ix
            if (!handFull) {
                assertThat(slots[ix])
                    .describedAs("Click on empty slot $ix with empty hand")
                    .isNotNull()
                hand = slots[ix]
                handFull = true
                slots[ix] = null
            } else if (slots[ix] == null) {
                slots[ix] = hand
                hand = null
                handFull = false
            } else {
                val temp = slots[ix]
                slots[ix] = hand
                hand = temp
            }
        }
        assertThat(handFull).describedAs("Hand should be empty after all clicks").isFalse()
        return slots
    }

    private fun <A> computeExpected(items: List<A?>, compare: Comparator<A>, splitAfter: Int?): List<A?> {
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
     * Run sortDescAndSplit, simulate the clicks, and verify the result matches the expected
     * target layout. Returns the click list for further assertions (e.g. click count).
     */
    private fun <A> assertSort(
        items: List<A?>,
        compare: Comparator<A>,
        splitAfter: Int? = null,
    ): List<PickDropSort.ClickOn> {
        val clicks = sort.sortDescAndSplit(items, compare, splitAfter)
        val result = simulate(items, clicks)
        val expected = computeExpected(items, compare, splitAfter)

        for (i in expected.indices) {
            if (expected[i] == null) {
                assertThat(result[i]).describedAs("Position $i should be null").isNull()
            } else {
                assertThat(result[i]).describedAs("Position $i should not be null").isNotNull()
                assertThat(compare.compare(result[i]!!, expected[i]!!))
                    .describedAs("Position $i: expected ${expected[i]}, got ${result[i]}")
                    .isEqualTo(0)
            }
        }
        return clicks
    }

    // -- Tests --

    @Nested
    inner class `trivial cases` {
        @Test
        fun `empty list`() {
            assertThat(assertSort(emptyList<Int?>(), intCompare)).isEmpty()
        }

        @Test
        fun `single item`() {
            assertThat(assertSort(listOf(42), intCompare)).isEmpty()
        }

        @Test
        fun `single null`() {
            assertThat(assertSort(listOf<Int?>(null), intCompare)).isEmpty()
        }

        @Test
        fun `all nulls`() {
            assertThat(assertSort(listOf<Int?>(null, null, null), intCompare)).isEmpty()
        }

        @Test
        fun `already sorted descending`() {
            assertThat(assertSort(listOf(3, 2, 1), intCompare)).isEmpty()
        }

        @Test
        fun `already sorted with trailing nulls`() {
            assertThat(assertSort(listOf(3, 2, null, null), intCompare)).isEmpty()
        }
    }

    @Nested
    inner class `sorting without split` {
        @Test
        fun `two items swapped`() {
            // [1,2] -> [2,1]: one 2-cycle, no null -> 3 clicks
            val clicks = assertSort(listOf(1, 2), intCompare)
            assertThat(clicks).hasSize(3)
        }

        @Test
        fun `three items reversed`() {
            // [1,2,3] -> [3,2,1]: pos 1 stays, (0,2) swap -> 3 clicks
            val clicks = assertSort(listOf(1, 2, 3), intCompare)
            assertThat(clicks).hasSize(3)
        }

        @Test
        fun `four items fully reversed`() {
            // [1,2,3,4] -> [4,3,2,1]: two 2-cycles (0,3) and (1,2) -> 3+3 = 6 clicks
            val clicks = assertSort(listOf(1, 2, 3, 4), intCompare)
            assertThat(clicks).hasSize(6)
        }

        @Test
        fun `with null in the middle`() {
            // [1, null, 2] -> [2, 1, null]: one 3-cycle with null -> 3 clicks
            val clicks = assertSort(listOf(1, null, 2), intCompare)
            assertThat(clicks).hasSize(3)
        }

        @Test
        fun `null at beginning`() {
            // [null, 1, 2] -> [2, 1, null]: pos 1 fixed, (0,2) 2-cycle with null -> 2 clicks
            val clicks = assertSort(listOf<Int?>(null, 1, 2), intCompare)
            assertThat(clicks).hasSize(2)
        }

        @Test
        fun `five items unsorted`() {
            assertSort(listOf(3, 1, 5, 2, 4), intCompare)
        }

        @Test
        fun `five items with nulls`() {
            assertSort(listOf(3, null, 5, 2, 4, null, 1), intCompare)
        }
    }

    @Nested
    inner class `sorting with split` {
        @Test
        fun `split after 1`() {
            // [1, 2, null] splitAfter=1 -> [2, null, 1]: cycle with null -> 3 clicks
            val clicks = assertSort(listOf(1, 2, null), intCompare, splitAfter = 1)
            assertThat(clicks).hasSize(3)
        }

        @Test
        fun `split after 0 - gap at beginning`() {
            // [2, null, 1] splitAfter=0 -> [null, 2, 1]
            assertSort(listOf(2, null, 1), intCompare, splitAfter = 0)
        }

        @Test
        fun `split after equals item count - same as no split`() {
            // [1, 2, null] splitAfter=2 -> [2, 1, null]
            val clicks = assertSort(listOf(1, 2, null), intCompare, splitAfter = 2)
            assertThat(clicks).hasSize(3)
        }

        @Test
        fun `multiple nulls with split`() {
            // [1, null, null, 2] splitAfter=1 -> [2, null, 1, null]
            assertSort(listOf(1, null, null, 2), intCompare, splitAfter = 1)
        }

        @Test
        fun `split with larger gap position`() {
            // [1, 2, 3, 4, null] splitAfter=2 -> [4, 3, null, 2, 1]
            assertSort(listOf(1, 2, 3, 4, null), intCompare, splitAfter = 2)
        }

        @Test
        fun `already in split position`() {
            // [3, null, 1, 2] splitAfter=1 -> [3, null, 2, 1]
            assertSort(listOf(3, null, 1, 2), intCompare, splitAfter = 1)
        }
    }

    @Nested
    inner class `duplicate values` {
        @Test
        fun `all same values - no clicks needed`() {
            assertThat(assertSort(listOf(5, 5, 5), intCompare)).isEmpty()
        }

        @Test
        fun `duplicates already sorted`() {
            assertThat(assertSort(listOf(3, 3, 1), intCompare)).isEmpty()
        }

        @Test
        fun `duplicates partially sorted`() {
            // [1, 3, 3] -> [3, 3, 1]: item at 0 and one 3 swap
            val clicks = assertSort(listOf(1, 3, 3), intCompare)
            assertThat(clicks).hasSize(3)
        }

        @Test
        fun `duplicates with null`() {
            assertSort(listOf(2, null, 2, 1), intCompare)
        }

        @Test
        fun `duplicates with split`() {
            assertSort(listOf(3, null, 3, 1), intCompare, splitAfter = 1)
        }
    }

    @Nested
    inner class `click count optimality` {
        @Test
        fun `cycle with null saves one click vs without`() {
            // 2-cycle without null: 3 clicks
            val noNull = assertSort(listOf(1, 2), intCompare)
            assertThat(noNull).hasSize(3)

            // 2-cycle with null: 2 clicks (null is part of the cycle)
            val withNull = assertSort(listOf(2, null, 1), intCompare, splitAfter = 0)
            // [2, null, 1] splitAfter=0 -> [null, 2, 1]: only pos 0 and 1 need to change -> 2 clicks
            assertThat(withNull).hasSize(2)
        }

        @Test
        fun `multiple independent cycles`() {
            // [2, 1, 4, 3] -> [4, 3, 2, 1]: two 2-cycles (0,2) and (1,3), no null -> 3+3 = 6
            val clicks = assertSort(listOf(2, 1, 4, 3), intCompare)
            assertThat(clicks).hasSize(6)
        }
    }
}
