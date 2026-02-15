package com.gh.om.ks.arpgmacro.overlay

import androidx.compose.foundation.background
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.width
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
import androidx.compose.ui.window.Window
import androidx.compose.ui.window.WindowPosition
import androidx.compose.ui.window.application
import androidx.compose.ui.window.rememberWindowState
import com.gh.om.ks.arpgmacro.core.overlay.OverlayEntry
import com.gh.om.ks.arpgmacro.core.overlay.OverlayOutput
import kotlin.concurrent.thread

class ComposeOverlayWindow : OverlayOutput {
    private var visible by mutableStateOf(false)
    private var entries by mutableStateOf(emptyList<OverlayEntry>())

    override fun show(entries: List<OverlayEntry>) {
        println("compose.show $this")
        this.entries = entries
        this.visible = true
    }

    override fun hide() {
        this.visible = false
    }

    /**
     * Starts the Compose overlay on a daemon thread.
     * Call once at startup. The overlay renders based on [show]/[hide] calls.
     */
    override fun start() {
        thread(isDaemon = true, name = "overlay-ui") {
            application(exitProcessOnExit = false) {
                Window(
                    onCloseRequest = {},
                    visible = visible,
                    transparent = true,
                    undecorated = true,
                    alwaysOnTop = true,
                    focusable = false,
                    resizable = false,
                    title = "OMKSM Overlay",
                    state = rememberWindowState(
                        position = WindowPosition(32.dp, 32.dp),
                        size = DpSize(320.dp, 400.dp),
                    ),
                ) {
                    OverlayContent(entries)
                }
            }
        }
    }
}

private val bgColor = Color(0xDD, 0x1a, 0x1a, 0x2e).copy(alpha = 0.87f)
private val categoryColor = Color(0xFF, 0xA0, 0xA0, 0xA0)
private val keyColor = Color(0xFF, 0x4F, 0xC3, 0xF7)
private val labelColor = Color(0xFF, 0xFA, 0xFA, 0xFA)

@Composable
private fun OverlayContent(entries: List<OverlayEntry>) {
    val grouped = entries.groupBy { it.category }

    Column(
        modifier = Modifier
            .background(bgColor, RoundedCornerShape(8.dp))
            .padding(12.dp)
    ) {
        var isFirst = true
        for ((category, items) in grouped) {
            if (category.isNotEmpty()) {
                Text(
                    text = category,
                    color = categoryColor,
                    fontSize = 11.sp,
                    modifier = Modifier.padding(
                        bottom = 4.dp,
                        top = if (isFirst) 0.dp else 8.dp,
                    ),
                )
            }
            for (entry in items) {
                Row(modifier = Modifier.padding(vertical = 2.dp)) {
                    Text(
                        text = entry.key,
                        color = keyColor,
                        fontSize = 14.sp,
                        modifier = Modifier.width(40.dp),
                    )
                    Text(
                        text = entry.label,
                        color = labelColor,
                        fontSize = 14.sp,
                    )
                }
            }
            isFirst = false
        }
    }
}
