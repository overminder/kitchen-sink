package macrocore

import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class ScreenConstantsTest {

    @Nested
    inner class GridGeneration {
        @Test
        fun `allGrids generates correct number of positions`() {
            val grids = PoeScreenConstants.allGrids(
                start = ScreenPoint(0, 0),
                rows = 3,
                columns = 4,
                gridSize = 10,
            ).toList()
            assertThat(grids).hasSize(12)
        }

        @Test
        fun `allGrids generates correct coordinates`() {
            val grids = PoeScreenConstants.allGrids(
                start = ScreenPoint(100, 200),
                rows = 2,
                columns = 2,
                gridSize = 50,
            ).toList()
            assertThat(grids).containsExactly(
                ScreenPoint(100, 200),
                ScreenPoint(100, 250),
                ScreenPoint(150, 200),
                ScreenPoint(150, 250),
            )
        }

        @Test
        fun `allGrids with single cell returns start point`() {
            val grids = PoeScreenConstants.allGrids(
                start = ScreenPoint(10, 20),
                rows = 1,
                columns = 1,
                gridSize = 70,
            ).toList()
            assertThat(grids).containsExactly(ScreenPoint(10, 20))
        }
    }

    @Nested
    inner class GridColorDetection {
        @Test
        fun `empty grid color is not detected as having item`() {
            assertThat(
                PoeScreenConstants.gridColorHasItem(PoeScreenConstants.emptyGridColor)
            ).isFalse()
        }

        @Test
        fun `non-empty color is detected as having item`() {
            assertThat(
                PoeScreenConstants.gridColorHasItem(ScreenColor(100, 100, 100))
            ).isTrue()
        }

        @Test
        fun `near-empty color within threshold is not detected`() {
            assertThat(
                PoeScreenConstants.gridColorHasItem(ScreenColor(8, 9, 10))
            ).isFalse()
        }
    }

    @Nested
    inner class SlotFiltering {
        @Test
        fun `filterOccupiedSlots returns only occupied positions`() {
            val screen = FakeScreen()
            val slots = PoeScreenConstants.allGrids(
                start = ScreenPoint(0, 0),
                rows = 2,
                columns = 2,
                gridSize = 10,
            )
            // Set only one slot to have an item
            screen.pixels = mapOf(
                ScreenPoint(0, 0) to ScreenColor(100, 100, 100),
            )
            // Default color (0,0,0) is close to emptyGridColor (7,8,9)
            screen.defaultColor = PoeScreenConstants.emptyGridColor

            val pixelSource = screen.captureScreen()
            val occupied = PoeScreenConstants.filterOccupiedSlots(slots, pixelSource)
            assertThat(occupied).containsExactly(ScreenPoint(0, 0))
        }
    }

    @Nested
    inner class Constants {
        @Test
        fun `secondItemInBag is one grid below first`() {
            val first = PoeScreenConstants.firstItemInBag
            val second = PoeScreenConstants.secondItemInBag
            assertThat(second.x).isEqualTo(first.x)
            assertThat(second.y).isEqualTo(first.y + PoeScreenConstants.bagGridSize)
        }
    }
}
