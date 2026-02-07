package macrocore

import kotlinx.coroutines.test.runTest
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class MultiRollLoopTest {
    private lateinit var keyboard: FakeKeyboardOutput
    private lateinit var mouse: FakeMouseOutput
    private lateinit var clipboard: FakeClipboard
    private lateinit var clock: FakeClock
    private lateinit var interactor: PoeInteractor
    private lateinit var loop: MultiRollLoop

    @BeforeEach
    fun setup() {
        keyboard = FakeKeyboardOutput()
        mouse = FakeMouseOutput()
        clipboard = FakeClipboard()
        clock = FakeClock()
        interactor = PoeInteractor(keyboard, mouse, clipboard, clock)
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

    private class FakeRerollProvider(var remaining: Int = 5) : RerollProvider {
        var applyCalls = 0
        override suspend fun hasMore() = remaining > 0
        override suspend fun applyTo(itemSlot: ScreenPoint, item: PoeRollableItem) {
            remaining--
            applyCalls++
        }
    }

    @Nested
    inner class BasicRolling {
        @Test
        fun `already-good items are accepted without rerolling`() = runTest {
            clipboard.content = """
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
            clipboard.content = """
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
            clipboard.content = """
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
    }

    @Nested
    inner class ReportGeneration {
        @Test
        fun `report contains roll counts`() = runTest {
            clipboard.content = """
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
