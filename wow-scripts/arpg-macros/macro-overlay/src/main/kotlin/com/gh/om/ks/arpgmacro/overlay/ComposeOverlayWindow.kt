package com.gh.om.ks.arpgmacro.overlay

import androidx.compose.foundation.background
import androidx.compose.foundation.border
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
import androidx.compose.material3.DropdownMenu
import androidx.compose.material3.DropdownMenuItem
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
import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.overlay.ActivationContext
import com.gh.om.ks.arpgmacro.core.overlay.BackgroundMacroState
import com.gh.om.ks.arpgmacro.core.overlay.BgMacroStatusLine
import com.gh.om.ks.arpgmacro.core.overlay.MacroRegistration
import com.gh.om.ks.arpgmacro.core.overlay.OverlayController
import com.gh.om.ks.arpgmacro.core.overlay.OverlaySelection
import com.gh.om.ks.arpgmacro.recipe.activeWindowFlow
import com.gh.om.ks.arpgmacro.recipe.poe.PoeFlasks
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.withTimeoutOrNull
import java.util.concurrent.CountDownLatch
import kotlin.concurrent.thread

private const val INACTIVITY_TIMEOUT_MS = 120_000L
private const val CONFIRM_COUNTDOWN_SECS = 3

class ComposeOverlayWindow(
    private val activeWindowChecker: ActiveWindowChecker,
    private val setClickThrough: (Boolean) -> Unit,
) : OverlayController {

    companion object {
        const val TITLE = "OMKSM Overlay"
    }

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

    /** Background macro state; set via [connectBackgroundMacros]. */
    @Volatile private var bgMacroState: BackgroundMacroState? = null

    /** Mirrors the latest value from the background macro runner's isEnabled flow. */
    private var bgMacrosEnabled by mutableStateOf(true)

    /** Mirrors the latest selected flask config from the runner's flow. */
    private var bgSelectedFlaskConfig by mutableStateOf<PoeFlasks.Config>(PoeFlasks.mbTincture)

    /** Mirrors the latest background macro status lines from the tracker. */
    private var bgStatusLines by mutableStateOf<List<BgMacroStatusLine>>(emptyList())

    /** True when a game window (from [BackgroundMacroState.gameTitles]) is in the foreground. */
    private var gameInForeground by mutableStateOf(false)

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
                val isVisible = pickerVisible || runningMacroName != null || (bgStatusLines.isNotEmpty() && gameInForeground)
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
                    title = TITLE,
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
                    LaunchedEffect(pickerVisible, runningMacroName, bgStatusLines.isNotEmpty()) {
                        windowState.size = computeWindowSize(
                            pickerVisible,
                            runningMacroName != null,
                            bgStatusLines.isNotEmpty(),
                        )
                    }

                    // Collect background macro enabled state from the runner's flow
                    val bgState = bgMacroState
                    if (bgState != null) {
                        LaunchedEffect(bgState) {
                            bgState.isEnabled.collect { bgMacrosEnabled = it }
                        }
                        LaunchedEffect(bgState) {
                            bgState.selectedFlaskConfig.collect { bgSelectedFlaskConfig = it }
                        }
                        LaunchedEffect(bgState) {
                            bgState.statusLines.collect { bgStatusLines = it }
                        }
                        // Poll foreground window; hide bg status when not in a game window
                        LaunchedEffect(bgState) {
                            activeWindowChecker.activeWindowFlow(bgState.gameTitles)
                                .collect { gameInForeground = it }
                        }
                    }

                    // Toggle click-through: disabled only while picker is interactive
                    LaunchedEffect(pickerVisible) {
                        setClickThrough(!pickerVisible)
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
                                bgState = bgState,
                                bgEnabled = bgMacrosEnabled,
                                bgSelectedFlaskConfig = bgSelectedFlaskConfig,
                            )
                        }
                    } else {
                        val running = runningMacroName
                        if (running != null) {
                            ExecutionStatusContent(running)
                        } else if (bgStatusLines.isNotEmpty()) {
                            BgMacroStatusContent(bgStatusLines)
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

    override fun overlayWindowTitle(): String = TITLE

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

    override fun connectBackgroundMacros(state: BackgroundMacroState) {
        bgMacroState = state
        bgMacrosEnabled = state.isEnabled.value
        bgSelectedFlaskConfig = state.selectedFlaskConfig.value
        bgStatusLines = state.statusLines.value
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

private val PICKER_SIZE = DpSize(320.dp, 460.dp)
private val STATUS_SIZE = DpSize(240.dp, 36.dp)
private val BG_STATUS_SIZE = DpSize(480.dp, 36.dp)

private fun computeWindowSize(
    pickerVisible: Boolean,
    hasRunning: Boolean,
    hasBgStatus: Boolean,
): DpSize = when {
    pickerVisible -> PICKER_SIZE
    hasRunning -> STATUS_SIZE
    hasBgStatus -> BG_STATUS_SIZE
    else -> STATUS_SIZE
}

// -- Colors --

private val bgColor = Color(0x1a, 0x1a, 0x2e).copy(alpha = 0.93f)
private val headerColor = Color(0xE0, 0xE0, 0xE0)
private val categoryColor = Color(0xA0, 0xA0, 0xA0)
private val shortcutColor = Color(0x4F, 0xC3, 0xF7)
private val labelColor = Color(0xFA, 0xFA, 0xFA)
private val labelColorOnLight = bgColor
private val escHintColor = Color(0x80, 0x80, 0x80)
private val confirmButtonColor = Color(0x4F, 0xC3, 0xF7)
private val bgOnColor = Color(0x4C, 0xAF, 0x50)
private val bgOffColor = Color(0x75, 0x75, 0x75)

// Pill colors for flask pattern visualization (one per Par group)
private val pillColors = listOf(
    Color(0x4F, 0xC3, 0xF7), // blue
    Color(0xFF, 0xB7, 0x4D), // orange
    Color(0x81, 0xC7, 0x84), // green
    Color(0xF0, 0x62, 0x92), // pink
    Color(0xCE, 0x93, 0xD8), // purple
)

// -- Composables --

@Composable
private fun OverlayContent(
    macros: List<MacroRegistration>,
    onSelect: (MacroRegistration) -> Unit,
    onCancel: () -> Unit,
    bgState: BackgroundMacroState?,
    bgEnabled: Boolean,
    bgSelectedFlaskConfig: PoeFlasks.Config,
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

        // BG macro controls at the bottom of picker
        if (bgState != null) {
            // Divider
            Box(
                modifier = Modifier
                    .fillMaxWidth()
                    .padding(top = 10.dp, bottom = 8.dp)
                    .height(0.5.dp)
                    .background(categoryColor.copy(alpha = 0.4f)),
            )
            BackgroundMacrosSection(
                bgEnabled = bgEnabled,
                onToggle = bgState.onToggle,
                availableConfigs = bgState.availableFlaskConfigs,
                selectedConfig = bgSelectedFlaskConfig,
                onSelectConfig = bgState.onSelectFlaskConfig,
            )
        }
    }

    // Request focus so keyboard events work immediately
    LaunchedEffect(Unit) {
        focusRequester.requestFocus()
    }
}

@Composable
private fun BackgroundMacrosSection(
    bgEnabled: Boolean,
    onToggle: () -> Unit,
    availableConfigs: List<Pair<String, PoeFlasks.Config>>,
    selectedConfig: PoeFlasks.Config,
    onSelectConfig: (PoeFlasks.Config) -> Unit,
) {
    val dotColor = if (bgEnabled) bgOnColor else bgOffColor
    val label = if (bgEnabled) "BG: ON" else "BG: OFF"
    var dropdownExpanded by remember { mutableStateOf(false) }
    val selectedName = availableConfigs.find { it.second == selectedConfig }?.first ?: "custom"

    Column(verticalArrangement = Arrangement.spacedBy(6.dp)) {
        // Toggle row
        Row(
            modifier = Modifier
                .fillMaxWidth()
                .clickable { onToggle() }
                .padding(vertical = 4.dp),
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

        // Flask config selector
        Row(
            verticalAlignment = Alignment.CenterVertically,
            horizontalArrangement = Arrangement.spacedBy(8.dp),
        ) {
            FlaskPatternVisual(config = selectedConfig)

            Box {
                Text(
                    text = selectedName,
                    color = shortcutColor,
                    fontSize = 12.sp,
                    modifier = Modifier
                        .clickable { dropdownExpanded = true }
                        .background(shortcutColor.copy(alpha = 0.08f), RoundedCornerShape(4.dp))
                        .padding(horizontal = 8.dp, vertical = 4.dp),
                )
                DropdownMenu(
                    expanded = dropdownExpanded,
                    onDismissRequest = { dropdownExpanded = false },
                ) {
                    for ((name, config) in availableConfigs) {
                        DropdownMenuItem(
                            text = {
                                Row(
                                    verticalAlignment = Alignment.CenterVertically,
                                    horizontalArrangement = Arrangement.spacedBy(8.dp),
                                ) {
                                    FlaskPatternVisual(config = config)
                                    Text(name, color = labelColorOnLight, fontSize = 13.sp)
                                }
                            },
                            onClick = {
                                onSelectConfig(config)
                                dropdownExpanded = false
                            },
                        )
                    }
                }
            }
        }
    }
}

/**
 * 5 vertical pill shapes representing flask slots 1-5.
 * - Filled pill = automated slot
 * - Outline-only pill = non-automated slot
 * - Color indicates group: same color = Alt (round-robin), different color = Par (independent)
 */
@Composable
private fun FlaskPatternVisual(config: PoeFlasks.Config) {
    val slotColors = computeSlotColors(config)

    Row(horizontalArrangement = Arrangement.spacedBy(3.dp)) {
        for (slot in 1..5) {
            val color = slotColors[slot]
            FlaskPill(color = color)
        }
    }
}

@Composable
private fun FlaskPill(color: Color?) {
    val pillShape = RoundedCornerShape(4.dp)
    if (color != null) {
        Box(
            modifier = Modifier
                .width(8.dp)
                .height(24.dp)
                .background(color.copy(alpha = 0.7f), pillShape),
        )
    } else {
        Box(
            modifier = Modifier
                .width(8.dp)
                .height(24.dp)
                .border(1.dp, categoryColor.copy(alpha = 0.5f), pillShape),
        )
    }
}

/**
 * Walks the Config tree and assigns a color to each flask slot (1-5).
 * Returns null for non-automated slots.
 * Color assignment: each top-level Par child gets a different color;
 * within an Alt group all children share the same color.
 */
private fun computeSlotColors(config: PoeFlasks.Config): Map<Int, Color?> {
    val result = mutableMapOf<Int, Color?>()
    assignColors(config, colorIndex = 0, result = result)
    return result
}

/** Returns the next color index after assigning colors for this config subtree. */
private fun assignColors(
    config: PoeFlasks.Config,
    colorIndex: Int,
    result: MutableMap<Int, Color?>,
): Int {
    return when (config) {
        is PoeFlasks.Config.One -> {
            result[config.key] = pillColors[colorIndex % pillColors.size]
            colorIndex + 1
        }
        is PoeFlasks.Config.Alt -> {
            // All children in an Alt group share the same color
            for (child in config.configs) {
                assignColors(child, colorIndex, result)
            }
            colorIndex + 1
        }
        is PoeFlasks.Config.Par -> {
            // Each child in a Par group gets a different color
            var nextIndex = colorIndex
            for (child in config.configs) {
                nextIndex = assignColors(child, nextIndex, result)
            }
            nextIndex
        }
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
private fun BgMacroStatusContent(statusLines: List<BgMacroStatusLine>) {
    Row(
        modifier = Modifier
            .background(bgColor.copy(alpha = 0.85f), RoundedCornerShape(6.dp))
            .padding(horizontal = 14.dp, vertical = 8.dp),
        verticalAlignment = Alignment.CenterVertically,
        horizontalArrangement = Arrangement.spacedBy(8.dp),
    ) {
        for ((index, line) in statusLines.withIndex()) {
            if (index > 0) {
                Text("│", color = categoryColor.copy(alpha = 0.5f), fontSize = 11.sp)
            }
            Text(formatStatusLine(line), color = labelColor, fontSize = 12.sp)
        }
    }
}

private fun formatStatusLine(line: BgMacroStatusLine): String {
    val keysPart = line.keyCounts.joinToString(", ") { (key, count) ->
        if (count == 1) key else "$key x$count"
    }
    val secs = line.runningDurationSecs
    val duration = "%02d:%02d".format(secs / 60, secs % 60)
    return "${line.macroName} [$keysPart] $duration"
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
