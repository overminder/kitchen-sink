package com.gh.om.ks.arpgmacro.overlay

import androidx.compose.foundation.background
import androidx.compose.foundation.clickable
import androidx.compose.foundation.focusable
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.layout.width
import androidx.compose.foundation.shape.CircleShape
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
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.withTimeoutOrNull
import java.util.concurrent.CountDownLatch
import kotlin.concurrent.thread

private const val OVERLAY_TITLE = "OMKSM Overlay"
private const val INACTIVITY_TIMEOUT_MS = 8_000L
private const val CONFIRM_COUNTDOWN_SECS = 3

class ComposeOverlayWindow : OverlayController {

    // -- State shared between coordinator coroutine and Compose UI thread --

    /** True while the picker / confirmation view is showing (window is focusable). */
    private var pickerVisible by mutableStateOf(false)
    private var macros by mutableStateOf(emptyList<MacroRegistration>())

    /**
     * Non-null when the confirmation view is showing.
     * Null means the picker view is active.
     */
    private var confirmingMacro by mutableStateOf<MacroRegistration?>(null)

    /**
     * Non-null while a macro is running — shows a click-through status badge.
     * The window becomes non-focusable in this state.
     */
    private var runningMacroName by mutableStateOf<String?>(null)

    /** True once [connectBackgroundMacros] has been called. Triggers badge visibility. */
    private var bgMacrosConnected by mutableStateOf(false)

    /** Mirrors the latest value from the background macro runner's isEnabled flow. */
    private var bgMacrosEnabled by mutableStateOf(true)

    /** The source of truth for background macro enabled state; collected inside the composable. */
    @Volatile private var bgEnabledFlow: StateFlow<Boolean>? = null

    /** Callback to toggle background macros; invoked from the badge click. */
    @Volatile private var bgToggleCallback: (() -> Unit)? = null

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
                val isVisible = pickerVisible || runningMacroName != null || bgMacrosConnected
                val windowState = rememberWindowState(
                    position = WindowPosition(32.dp, 32.dp),
                    size = PICKER_SIZE,
                )

                Window(
                    onCloseRequest = { cancel() },
                    visible = isVisible,
                    transparent = true,
                    undecorated = true,
                    alwaysOnTop = true,
                    focusable = pickerVisible,
                    resizable = false,
                    title = OVERLAY_TITLE,
                    state = windowState,
                    onPreviewKeyEvent = { keyEvent ->
                        if (keyEvent.type == KeyEventType.KeyDown) {
                            handleKeyEvent(keyEvent.key)
                        } else {
                            false
                        }
                    },
                ) {
                    // Sync window size to current display mode
                    LaunchedEffect(pickerVisible, runningMacroName, bgMacrosConnected) {
                        windowState.size = computeWindowSize(
                            pickerVisible,
                            runningMacroName != null,
                            bgMacrosConnected,
                        )
                    }

                    // Collect background macro enabled state from the runner's flow
                    LaunchedEffect(bgMacrosConnected) {
                        bgEnabledFlow?.collect { bgMacrosEnabled = it }
                    }

                    if (pickerVisible) {
                        val confirming = confirmingMacro
                        if (confirming != null) {
                            ConfirmationContent(
                                registration = confirming,
                                onConfirm = { complete(OverlaySelection.Selected(confirming)) },
                                onCancel = { cancel() },
                            )
                        } else {
                            OverlayContent(
                                macros = macros,
                                onSelect = { reg -> confirmingMacro = reg },
                                onCancel = { cancel() },
                            )
                        }
                    } else {
                        Column(verticalArrangement = Arrangement.spacedBy(4.dp)) {
                            val running = runningMacroName
                            if (running != null) {
                                ExecutionStatusContent(running)
                            }
                            if (bgMacrosConnected) {
                                BackgroundMacrosBadge(
                                    enabled = bgMacrosEnabled,
                                    onToggle = { bgToggleCallback?.invoke() },
                                )
                            }
                        }
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
        this.pickerVisible = true

        return try {
            withTimeoutOrNull(INACTIVITY_TIMEOUT_MS) {
                deferred.await()
            } ?: OverlaySelection.Cancelled
        } finally {
            this.pickerVisible = false
            this.confirmingMacro = null
            pendingSelection = null
        }
    }

    override fun showExecutionStatus(macroName: String) {
        runningMacroName = macroName
    }

    override fun hideExecutionStatus() {
        runningMacroName = null
    }

    override fun connectBackgroundMacros(isEnabled: StateFlow<Boolean>, onToggle: () -> Unit) {
        bgEnabledFlow = isEnabled
        bgToggleCallback = onToggle
        bgMacrosEnabled = isEnabled.value
        bgMacrosConnected = true
    }

    // -- Internal helpers --

    private fun complete(selection: OverlaySelection) {
        pendingSelection?.complete(selection)
    }

    private fun cancel() {
        complete(OverlaySelection.Cancelled)
    }

    private fun handleKeyEvent(key: Key): Boolean {
        val confirming = confirmingMacro
        if (confirming != null) {
            return when (key) {
                Key.Escape -> { cancel(); true }
                Key.Enter -> { complete(OverlaySelection.Selected(confirming)); true }
                else -> false
            }
        }

        // Picker mode
        when (key) {
            Key.Escape -> { cancel(); return true }
        }
        val index = when (key) {
            Key.One -> 0; Key.Two -> 1; Key.Three -> 2
            Key.Four -> 3; Key.Five -> 4; Key.Six -> 5
            Key.Seven -> 6; Key.Eight -> 7; Key.Nine -> 8
            else -> return false
        }
        val reg = macros.getOrNull(index) ?: return false
        confirmingMacro = reg
        return true
    }
}

// -- Window sizing --

private val PICKER_SIZE = DpSize(320.dp, 420.dp)
private val BADGE_SIZE = DpSize(200.dp, 36.dp)
private val STATUS_SIZE = DpSize(240.dp, 36.dp)
private val STATUS_AND_BADGE_SIZE = DpSize(240.dp, 76.dp)

private fun computeWindowSize(
    pickerVisible: Boolean,
    hasRunning: Boolean,
    hasBadge: Boolean,
): DpSize = when {
    pickerVisible -> PICKER_SIZE
    hasRunning && hasBadge -> STATUS_AND_BADGE_SIZE
    hasRunning -> STATUS_SIZE
    else -> BADGE_SIZE
}

// -- Colors --

private val bgColor = Color(0x1a, 0x1a, 0x2e).copy(alpha = 0.93f)
private val headerColor = Color(0xE0, 0xE0, 0xE0)
private val categoryColor = Color(0xA0, 0xA0, 0xA0)
private val shortcutColor = Color(0x4F, 0xC3, 0xF7)
private val labelColor = Color(0xFA, 0xFA, 0xFA)
private val escHintColor = Color(0x80, 0x80, 0x80)
private val confirmButtonColor = Color(0x4F, 0xC3, 0xF7)
private val bgOnColor = Color(0x4C, 0xAF, 0x50)
private val bgOffColor = Color(0x75, 0x75, 0x75)

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
private fun ConfirmationContent(
    registration: MacroRegistration,
    onConfirm: () -> Unit,
    onCancel: () -> Unit,
) {
    val focusRequester = remember { FocusRequester() }
    var countdown by remember(registration.id) { mutableStateOf(CONFIRM_COUNTDOWN_SECS) }

    // Auto-confirm countdown
    LaunchedEffect(registration.id) {
        repeat(CONFIRM_COUNTDOWN_SECS) {
            delay(1_000L)
            countdown--
        }
        onConfirm()
    }

    Column(
        modifier = Modifier
            .background(bgColor, RoundedCornerShape(8.dp))
            .padding(12.dp)
            .focusRequester(focusRequester)
            .focusable()
    ) {
        // Header: macro name
        Text(
            text = registration.name,
            color = headerColor,
            fontSize = 15.sp,
            modifier = Modifier.padding(bottom = 8.dp),
        )

        // Divider
        Box(
            modifier = Modifier
                .fillMaxWidth()
                .height(0.5.dp)
                .background(categoryColor.copy(alpha = 0.4f)),
        )

        // Description
        if (registration.description.isNotEmpty()) {
            Text(
                text = registration.description,
                color = labelColor,
                fontSize = 13.sp,
                lineHeight = 18.sp,
                modifier = Modifier.padding(top = 12.dp, bottom = 4.dp),
            )
        }

        // Countdown
        Text(
            text = "Starting in ${countdown}s…",
            color = shortcutColor,
            fontSize = 13.sp,
            modifier = Modifier.padding(top = 12.dp, bottom = 16.dp),
        )

        // Action buttons
        Row(
            modifier = Modifier.fillMaxWidth(),
            horizontalArrangement = Arrangement.SpaceBetween,
            verticalAlignment = Alignment.CenterVertically,
        ) {
            Text(
                text = "Go now",
                color = confirmButtonColor,
                fontSize = 14.sp,
                modifier = Modifier
                    .clickable { onConfirm() }
                    .background(confirmButtonColor.copy(alpha = 0.12f), RoundedCornerShape(4.dp))
                    .padding(horizontal = 16.dp, vertical = 8.dp),
            )
            Text(
                text = "Cancel",
                color = escHintColor,
                fontSize = 14.sp,
                modifier = Modifier
                    .clickable { onCancel() }
                    .padding(horizontal = 16.dp, vertical = 8.dp),
            )
        }
    }

    LaunchedEffect(Unit) {
        focusRequester.requestFocus()
    }
}

@Composable
private fun ExecutionStatusContent(macroName: String) {
    Row(
        modifier = Modifier
            .background(bgColor.copy(alpha = 0.85f), RoundedCornerShape(6.dp))
            .padding(horizontal = 14.dp, vertical = 8.dp),
        verticalAlignment = Alignment.CenterVertically,
        horizontalArrangement = Arrangement.spacedBy(8.dp),
    ) {
        Text("▶", color = shortcutColor, fontSize = 12.sp)
        Text(macroName, color = labelColor, fontSize = 13.sp)
    }
}

@Composable
private fun BackgroundMacrosBadge(enabled: Boolean, onToggle: () -> Unit) {
    val dotColor = if (enabled) bgOnColor else bgOffColor
    val label = if (enabled) "BG macros: ON" else "BG macros: OFF"
    Row(
        modifier = Modifier
            .background(bgColor.copy(alpha = 0.85f), RoundedCornerShape(6.dp))
            .clickable { onToggle() }
            .padding(horizontal = 12.dp, vertical = 8.dp),
        verticalAlignment = Alignment.CenterVertically,
        horizontalArrangement = Arrangement.spacedBy(8.dp),
    ) {
        Box(
            modifier = Modifier
                .size(8.dp)
                .background(dotColor, CircleShape),
        )
        Text(label, color = labelColor, fontSize = 12.sp)
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
