package com.gh.om.ks.arpgmacro.overlay

import androidx.compose.foundation.background
import androidx.compose.foundation.clickable
import androidx.compose.foundation.focusable
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.width
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.focus.FocusRequester
import androidx.compose.ui.focus.focusRequester
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.input.key.Key
import androidx.compose.ui.input.key.KeyEventType
import androidx.compose.ui.input.key.key
import androidx.compose.ui.input.key.onPreviewKeyEvent
import androidx.compose.ui.input.key.type
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
import androidx.compose.ui.window.Window
import androidx.compose.ui.window.WindowPosition
import androidx.compose.ui.window.application
import androidx.compose.ui.window.rememberWindowState
import com.gh.om.ks.arpgmacro.core.overlay.ActivationContext
import com.gh.om.ks.arpgmacro.core.overlay.MacroRegistration
import com.gh.om.ks.arpgmacro.core.overlay.OverlayController
import com.gh.om.ks.arpgmacro.core.overlay.OverlaySelection
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.withTimeoutOrNull
import java.util.concurrent.CountDownLatch
import kotlin.concurrent.thread

private const val OVERLAY_TITLE = "OMKSM Overlay"
private const val INACTIVITY_TIMEOUT_MS = 8_000L

class ComposeOverlayWindow : OverlayController {

    // -- State shared between coordinator coroutine and Compose UI thread --

    private var visible by mutableStateOf(false)
    private var macros by mutableStateOf(emptyList<MacroRegistration>())

    /**
     * Completes when the user selects a macro or cancels.
     * Null when the overlay is not showing.
     */
    @Volatile
    private var pendingSelection: CompletableDeferred<OverlaySelection>? = null

    /** Set after the Compose application loop starts and the window is realized. */
    @Volatile
    private var windowReady = false
    private val startedLatch = CountDownLatch(1)

    // -- OverlayController implementation --

    override fun start() {
        thread(isDaemon = true, name = "overlay-ui") {
            application(exitProcessOnExit = false) {
                Window(
                    onCloseRequest = { cancel() },
                    visible = visible,
                    transparent = true,
                    undecorated = true,
                    alwaysOnTop = true,
                    focusable = true,
                    resizable = false,
                    title = OVERLAY_TITLE,
                    state = rememberWindowState(
                        position = WindowPosition(32.dp, 32.dp),
                        size = DpSize(320.dp, 420.dp),
                    ),
                    onPreviewKeyEvent = { keyEvent ->
                        if (keyEvent.type == KeyEventType.KeyDown) {
                            handleKeyEvent(keyEvent.key)
                        } else {
                            false
                        }
                    },
                ) {
                    if (visible) {
                        OverlayContent(
                            macros = macros,
                            onSelect = { reg -> complete(OverlaySelection.Selected(reg)) },
                            onCancel = { cancel() },
                        )
                    }

                    // Signal that the window is realized
                    LaunchedEffect(Unit) {
                        windowReady = true
                        startedLatch.countDown()
                    }
                }
            }
        }
        // Wait for the Compose window to be realized before returning
        startedLatch.await()
    }

    override fun overlayWindowTitle(): String = OVERLAY_TITLE

    override suspend fun awaitSelection(
        macros: List<MacroRegistration>,
        context: ActivationContext,
    ): OverlaySelection {
        val deferred = CompletableDeferred<OverlaySelection>()
        pendingSelection = deferred

        // Update compose state to show the overlay
        this.macros = macros
        this.visible = true

        return try {
            withTimeoutOrNull(INACTIVITY_TIMEOUT_MS) {
                deferred.await()
            } ?: OverlaySelection.Cancelled
        } finally {
            this.visible = false
            pendingSelection = null
        }
    }

    // -- Internal helpers --

    private fun complete(selection: OverlaySelection) {
        pendingSelection?.complete(selection)
    }

    private fun cancel() {
        complete(OverlaySelection.Cancelled)
    }

    private fun handleKeyEvent(key: Key): Boolean {
        when (key) {
            Key.Escape -> {
                cancel()
                return true
            }
            // Number keys 1-9 for positional selection
            Key.One, Key.Two, Key.Three, Key.Four, Key.Five,
            Key.Six, Key.Seven, Key.Eight, Key.Nine -> {
                val index = when (key) {
                    Key.One -> 0; Key.Two -> 1; Key.Three -> 2
                    Key.Four -> 3; Key.Five -> 4; Key.Six -> 5
                    Key.Seven -> 6; Key.Eight -> 7; Key.Nine -> 8
                    else -> return false
                }
                val currentMacros = macros
                if (index < currentMacros.size) {
                    complete(OverlaySelection.Selected(currentMacros[index]))
                    return true
                }
            }
        }
        return false
    }
}

// -- Colors --

private val bgColor = Color(0x1a, 0x1a, 0x2e).copy(alpha = 0.93f)
private val headerColor = Color(0xE0, 0xE0, 0xE0)
private val categoryColor = Color(0xA0, 0xA0, 0xA0)
private val shortcutColor = Color(0x4F, 0xC3, 0xF7)
private val labelColor = Color(0xFA, 0xFA, 0xFA)
private val escHintColor = Color(0x80, 0x80, 0x80)

// -- Composables --

@Composable
private fun OverlayContent(
    macros: List<MacroRegistration>,
    onSelect: (MacroRegistration) -> Unit,
    onCancel: () -> Unit,
) {
    val focusRequester = remember { FocusRequester() }
    val grouped = macros.groupBy { it.category }

    // Auto-assign positional shortcut numbers across all macros
    var shortcutCounter = 1

    Column(
        modifier = Modifier
            .background(bgColor, RoundedCornerShape(8.dp))
            .padding(12.dp)
            .focusRequester(focusRequester)
            .focusable()
    ) {
        // Header
        Row(
            modifier = Modifier.fillMaxWidth().padding(bottom = 8.dp),
            horizontalArrangement = Arrangement.SpaceBetween,
            verticalAlignment = Alignment.CenterVertically,
        ) {
            Text("Select Macro", color = headerColor, fontSize = 15.sp)
            Text(
                text = "Esc ×",
                color = escHintColor,
                fontSize = 12.sp,
                modifier = Modifier.clickable { onCancel() },
            )
        }

        var isFirst = true
        for ((category, items) in grouped) {
            if (category.isNotEmpty()) {
                Text(
                    text = category,
                    color = categoryColor,
                    fontSize = 11.sp,
                    modifier = Modifier.padding(
                        bottom = 4.dp,
                        top = if (isFirst) 0.dp else 10.dp,
                    ),
                )
            }
            for (reg in items) {
                val shortcut = shortcutCounter++
                MacroRow(
                    shortcut = shortcut.toString(),
                    registration = reg,
                    onClick = { onSelect(reg) },
                )
            }
            isFirst = false
        }
    }

    // Request focus so keyboard events work immediately
    LaunchedEffect(Unit) {
        focusRequester.requestFocus()
    }
}

@Composable
private fun MacroRow(
    shortcut: String,
    registration: MacroRegistration,
    onClick: () -> Unit,
) {
    Row(
        modifier = Modifier
            .fillMaxWidth()
            .clickable { onClick() }
            .padding(vertical = 4.dp, horizontal = 4.dp),
        verticalAlignment = Alignment.CenterVertically,
    ) {
        Text(
            text = shortcut,
            color = shortcutColor,
            fontSize = 14.sp,
            modifier = Modifier.width(28.dp),
        )
        Text(
            text = registration.name,
            color = labelColor,
            fontSize = 14.sp,
            modifier = Modifier.weight(1f),
        )
        if (registration.gameFilter.isNotEmpty()) {
            Text(
                text = registration.gameFilter.joinToString("/"),
                color = categoryColor,
                fontSize = 11.sp,
            )
        }
    }
}
