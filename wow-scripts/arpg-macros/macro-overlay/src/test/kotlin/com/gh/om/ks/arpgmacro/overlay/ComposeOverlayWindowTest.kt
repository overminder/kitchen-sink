@file:OptIn(ExperimentalCoroutinesApi::class)

package com.gh.om.ks.arpgmacro.overlay

import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.ScreenPoint
import com.gh.om.ks.arpgmacro.core.overlay.ActivationContext
import com.gh.om.ks.arpgmacro.core.overlay.MacroRegistration
import com.gh.om.ks.arpgmacro.core.overlay.OverlaySelection
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.async
import kotlinx.coroutines.test.advanceTimeBy
import kotlinx.coroutines.test.advanceUntilIdle
import kotlinx.coroutines.test.runTest
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test

/**
 * Tests for [ComposeOverlayWindow] selection logic (without the Compose UI).
 *
 * Focus-loss auto-cancel is implemented via a Compose LaunchedEffect and
 * cannot be tested without the Compose runtime. These tests verify the
 * underlying selection/cancellation contract that the LaunchedEffect relies on.
 */
class ComposeOverlayWindowTest {

    private val activeWindowChecker = FakeActiveWindowChecker()

    private fun overlay() = ComposeOverlayWindow(
        activeWindowChecker = activeWindowChecker,
        setClickThrough = {},
        stealFocus = {},
    )

    private val testContext = ActivationContext(
        gameWindowHandle = null,
        gameTitle = "Path of Exile",
        cursorPosition = ScreenPoint(100, 100),
    )

    private val testMacros = listOf(
        MacroRegistration(
            id = "test",
            name = "Test Macro",
            category = "test",
            description = "desc",
            gameFilter = emptySet(),
        )
    )

    @Test
    fun `cancelSelection completes awaitSelection with Cancelled`() = runTest {
        val overlay = overlay()
        val result = async { overlay.awaitSelection(testMacros, testContext) }
        // Use advanceTimeBy instead of advanceUntilIdle to avoid triggering
        // the 120s inactivity timeout in virtual time
        advanceTimeBy(100)

        // Selection is pending
        assertThat(result.isActive).isTrue()

        // External cancellation (e.g., from focus-loss LaunchedEffect or leader key toggle)
        overlay.cancelSelection()
        advanceUntilIdle()

        assertThat(result.isCompleted).isTrue()
        assertThat(result.await()).isEqualTo(OverlaySelection.Cancelled)
    }

    @Test
    fun `cancelSelection is idempotent`() = runTest {
        val overlay = overlay()
        val result = async { overlay.awaitSelection(testMacros, testContext) }
        advanceTimeBy(100)

        overlay.cancelSelection()
        overlay.cancelSelection() // second call is no-op
        advanceUntilIdle()

        assertThat(result.await()).isEqualTo(OverlaySelection.Cancelled)
    }
}

private class FakeActiveWindowChecker : ActiveWindowChecker {
    @Volatile
    var activeTitle: String = ""
    override fun isActiveWindow(anyTitles: Collection<String>): Boolean =
        anyTitles.contains(activeTitle)
}
