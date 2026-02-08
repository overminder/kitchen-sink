package com.gh.om.ks.arpgmacro.core

import kotlinx.coroutines.test.runTest
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class MultiRollLoopTest {
    private lateinit var interactor: FakePoeInteractor
    private lateinit var mouse: FakeMouseOutput
    private lateinit var clock: FakeClock
    private lateinit var loop: MultiRollLoop

    @BeforeEach
    fun setup() {
        interactor = FakePoeInteractor()
        mouse = FakeMouseOutput()
        clock = FakeClock()
        loop = MultiRollLoop(interactor, mouse, clock)
    }

    private data class SimpleCheck(override val isGood: Boolean) : CheckResult

    private class AlwaysGoodChecker : ItemChecker<SimpleCheck> {
        override fun evaluate(item: PoeRollableItem) = SimpleCheck(true)
        override fun generateReport(results: List<SimpleCheck>) =
            "${results.size} items, all good"
    }

    private class AlwaysBadChecker : ItemChecker<SimpleCheck> {
        override fun evaluate(item: PoeRollableItem) = SimpleCheck(false)
        override fun generateReport(results: List<SimpleCheck>) =
            "${results.size} items processed"
    }

    /** Checker that considers items good only if Item Quantity >= threshold. */
    private class QuantityThresholdChecker(private val threshold: Int) : ItemChecker<SimpleCheck> {
        override fun evaluate(item: PoeRollableItem): SimpleCheck {
            val qty = item.qualities.firstOrNull {
                it.name == PoeRollableItem.QualName.Native(PoeRollableItem.AugType.Generic)
            }?.value ?: 0
            return SimpleCheck(qty >= threshold)
        }
        override fun generateReport(results: List<SimpleCheck>) =
            "${results.count { it.isGood }}/${results.size} passed"
    }

    private class FakeRerollProvider(var remaining: Int = 5) : RerollProvider {
        var applyCalls = 0
        var onApply: (suspend () -> Unit)? = null
        override suspend fun hasMore() = remaining > 0
        override suspend fun applyTo(itemSlot: ScreenPoint, item: PoeRollableItem) {
            remaining--
            applyCalls++
            onApply?.invoke()
        }
    }

    private val goodMapDescription = """
Item Class: Maps
Rarity: Rare
Good Map
Test Map
--------
Map Tier: 16
Item Quantity: +80% (augmented)
--------
Item Level: 83
--------
{ Prefix Modifier "Fecund" (Tier: 3) }
55% more Monster Life

--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
    """.trimIndent()

    private val badMapDescription = """
Item Class: Maps
Rarity: Rare
Bad Map
Test Map
--------
Map Tier: 16
Item Quantity: +30% (augmented)
--------
Item Level: 83
--------
{ Prefix Modifier "Fecund" (Tier: 3) }
55% more Monster Life

--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
    """.trimIndent()

    @Nested
    inner class BasicRolling {
        @Test
        fun `already-good items are accepted without rerolling`() = runTest {
            interactor.itemDescription = goodMapDescription

            val provider = FakeRerollProvider(remaining = 10)
            val report = loop.rollItems(
                checker = AlwaysGoodChecker(),
                itemsToRoll = listOf(ScreenPoint(100, 100)),
                rerollProvider = provider,
                shouldContinue = { true },
            )

            assertThat(report.itemsRolled).isEqualTo(1)
            assertThat(report.totalRerolls).isEqualTo(0)
            assertThat(provider.applyCalls).isEqualTo(0)
        }

        @Test
        fun `stops when currency runs out`() = runTest {
            interactor.itemDescription = badMapDescription

            val provider = FakeRerollProvider(remaining = 3)
            val report = loop.rollItems(
                checker = AlwaysBadChecker(),
                itemsToRoll = listOf(ScreenPoint(100, 100)),
                rerollProvider = provider,
                shouldContinue = { true },
            )

            assertThat(report.totalRerolls).isEqualTo(3)
            assertThat(report.itemsRolled).isEqualTo(0)
        }

        @Test
        fun `stops when shouldContinue returns false`() = runTest {
            interactor.itemDescription = badMapDescription

            var iterations = 0
            val report = loop.rollItems(
                checker = AlwaysBadChecker(),
                itemsToRoll = listOf(ScreenPoint(100, 100)),
                rerollProvider = FakeRerollProvider(remaining = 100),
                shouldContinue = {
                    iterations++
                    iterations <= 2
                },
            )

            assertThat(report.itemsRolled).isEqualTo(0)
        }

        @Test
        fun `reroll changes item from bad to good`() = runTest {
            interactor.itemDescription = badMapDescription

            // Checker that considers items good only if quantity >= 80
            val checker = QuantityThresholdChecker(80)

            val provider = FakeRerollProvider(remaining = 10)
            provider.onApply = {
                // Simulate the reroll changing the item
                interactor.itemDescription = goodMapDescription
            }

            val report = loop.rollItems(
                checker = checker,
                itemsToRoll = listOf(ScreenPoint(100, 100)),
                rerollProvider = provider,
                shouldContinue = { true },
            )

            assertThat(report.itemsRolled).isEqualTo(1)
            assertThat(report.totalRerolls).isEqualTo(1)
            assertThat(provider.applyCalls).isEqualTo(1)
        }
    }

    @Nested
    inner class ReportGeneration {
        @Test
        fun `report contains roll counts`() = runTest {
            interactor.itemDescription = goodMapDescription

            val report = loop.rollItems(
                checker = AlwaysGoodChecker(),
                itemsToRoll = listOf(ScreenPoint(100, 100), ScreenPoint(200, 200)),
                rerollProvider = FakeRerollProvider(remaining = 10),
                shouldContinue = { true },
            )

            assertThat(report.details).contains("Rolled 2 items")
            assertThat(report.details).contains("0 tries")
        }
    }
}
