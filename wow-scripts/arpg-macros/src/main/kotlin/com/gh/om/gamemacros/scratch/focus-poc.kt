package com.gh.om.gamemacros.scratch

import com.github.kwhat.jnativehook.GlobalScreen
import com.github.kwhat.jnativehook.keyboard.NativeKeyEvent
import com.github.kwhat.jnativehook.keyboard.NativeKeyListener
import com.sun.jna.Native
import com.sun.jna.platform.win32.User32
import com.sun.jna.platform.win32.WinDef.DWORD
import com.sun.jna.platform.win32.WinDef.HWND
import com.sun.jna.platform.win32.WinDef.LONG
import com.sun.jna.platform.win32.WinDef.WORD
import com.sun.jna.platform.win32.WinUser
import com.sun.jna.platform.win32.WinUser.INPUT
import java.awt.Color
import java.awt.Font
import java.awt.event.WindowEvent
import java.awt.event.WindowFocusListener
import javax.swing.JFrame
import javax.swing.JLabel
import javax.swing.SwingConstants
import javax.swing.SwingUtilities

/**
 * Context: task/attachment/focus-poc-spec.md
 * Phase 0: Focus interception PoC
 *
 * Standalone experiment to verify that a JVM process can reliably steal and return
 * window focus on Windows, with acceptable latency for the overlay UX.
 *
 * Usage:
 *   1. Run this main()
 *   2. Switch to a game (or any fullscreen/borderless window)
 *   3. Press Alt+X to trigger focus steal
 *   4. Overlay grabs focus for 3 seconds, then returns it
 *   5. Watch stdout for timing logs
 *
 * Press Alt+Q to quit.
 */

private val user32 = User32.INSTANCE

// --- Focus steal approaches ---

enum class FocusApproach(val label: String) {
    DIRECT("direct SetForegroundWindow"),
    ALT_WORKAROUND("SendInput Alt + SetForegroundWindow"),
}

/**
 * Approach (a): Just call SetForegroundWindow directly.
 * Might work because JNativeHook hooks receive input events,
 * and Windows allows the process that "received the last input event" to steal focus.
 */
private fun tryDirectSetForeground(hwnd: HWND): Boolean {
    return user32.SetForegroundWindow(hwnd)
}

/**
 * Approach (b): Simulate an Alt keypress via SendInput before SetForegroundWindow.
 * This is the most commonly used workaround (used by PowerToys, AutoHotkey, etc.).
 * The Alt press/release tricks Windows into thinking our process owns the input queue.
 */
private fun tryAltWorkaround(hwnd: HWND): Boolean {
    // Send Alt key down then up — must use toArray() for contiguous memory
    @Suppress("UNCHECKED_CAST")
    val inputs = INPUT().toArray(2) as Array<INPUT>

    // Alt down
    inputs[0].type = DWORD(INPUT.INPUT_KEYBOARD.toLong())
    inputs[0].input.setType("ki")
    inputs[0].input.ki.wVk = WORD(WinUser.VK_MENU.toLong())
    inputs[0].input.ki.dwFlags = DWORD(0) // key down

    // Alt up
    inputs[1].type = DWORD(INPUT.INPUT_KEYBOARD.toLong())
    inputs[1].input.setType("ki")
    inputs[1].input.ki.wVk = WORD(WinUser.VK_MENU.toLong())
    inputs[1].input.ki.dwFlags = DWORD(WinUser.KEYBDINPUT.KEYEVENTF_KEYUP.toLong())

    val sent = user32.SendInput(DWORD(2), inputs, inputs[0].size())
    if (sent.toInt() != 2) {
        println("  [WARN] SendInput returned ${sent.toInt()}, expected 2")
    }
    return user32.SetForegroundWindow(hwnd)
}

// --- Focus polling ---

/**
 * Poll GetForegroundWindow() every [intervalMs] until it matches [targetHwnd],
 * or timeout after [timeoutMs].
 * Returns true if focus was confirmed, false on timeout.
 */
private fun pollForegroundWindow(targetHwnd: HWND, timeoutMs: Long = 500, intervalMs: Long = 1): Boolean {
    val deadline = System.nanoTime() + timeoutMs * 1_000_000
    while (System.nanoTime() < deadline) {
        val current = user32.GetForegroundWindow()
        if (current != null && current.pointer == targetHwnd.pointer) {
            return true
        }
        Thread.sleep(intervalMs)
    }
    return false
}

// --- Swing overlay ---

private fun createOverlayFrame(): JFrame {
    val frame = JFrame("FocusPoc Overlay")
    frame.isUndecorated = true
    frame.isAlwaysOnTop = true
    frame.setSize(400, 200)
    frame.setLocationRelativeTo(null) // center on screen
    frame.background = Color(30, 30, 30, 220)
    // Semi-transparent content pane
    frame.contentPane.background = Color(30, 30, 30)

    val label = JLabel("IDLE", SwingConstants.CENTER)
    label.font = Font("Consolas", Font.BOLD, 24)
    label.foreground = Color.WHITE
    label.name = "statusLabel"
    frame.contentPane.add(label)

    // Log focus events on the frame itself
    frame.addWindowFocusListener(object : WindowFocusListener {
        override fun windowGainedFocus(e: WindowEvent) {
            println("  [SWING] Overlay gained focus")
        }

        override fun windowLostFocus(e: WindowEvent) {
            println("  [SWING] Overlay lost focus")
        }
    })

    frame.isVisible = true
    return frame
}

private fun setOverlayText(frame: JFrame, text: String) {
    SwingUtilities.invokeLater {
        val label = frame.contentPane.getComponent(0) as JLabel
        label.text = text
    }
}

private fun getHwndForFrame(frame: JFrame): HWND? {
    // Use FindWindowW by title — more reliable than Native.getWindowPointer for Swing
    return user32.FindWindow(null, frame.title)
}

// --- Main flow ---

@Volatile
private var running = true

@Volatile
private var focusFlowInProgress = false

private fun runFocusFlow(overlayFrame: JFrame, overlayHwnd: HWND, trialNumber: Int) {
    if (focusFlowInProgress) {
        println("[$trialNumber] Focus flow already in progress, skipping")
        return
    }
    focusFlowInProgress = true

    Thread {
        try {
            println("\n========== Trial #$trialNumber ==========")

            // 1. Record previous foreground window
            val previousHwnd = user32.GetForegroundWindow()
            println("[$trialNumber] Previous foreground HWND: $previousHwnd")
            if (previousHwnd == null) {
                println("[$trialNumber] No foreground window — aborting")
                return@Thread
            }

            // Get the previous window title for logging
            val titleBuf = CharArray(256)
            user32.GetWindowText(previousHwnd, titleBuf, titleBuf.size)
            println("[$trialNumber] Previous window title: ${String(titleBuf).trimEnd('\u0000')}")

            // 2. Try approach (a): direct SetForegroundWindow
            val t0 = System.nanoTime()
            println("[$trialNumber] Trying approach (a): direct SetForegroundWindow...")
            val directResult = tryDirectSetForeground(overlayHwnd)
            println("[$trialNumber]   SetForegroundWindow returned: $directResult")

            val stealApproach: FocusApproach
            val stealConfirmed: Boolean

            if (directResult && pollForegroundWindow(overlayHwnd, timeoutMs = 100)) {
                stealApproach = FocusApproach.DIRECT
                stealConfirmed = true
            } else {
                // 3. Try approach (b): Alt workaround
                println("[$trialNumber] Approach (a) failed or timed out, trying (b): Alt workaround...")
                val altResult = tryAltWorkaround(overlayHwnd)
                println("[$trialNumber]   SetForegroundWindow (after Alt) returned: $altResult")
                stealApproach = FocusApproach.ALT_WORKAROUND
                stealConfirmed = pollForegroundWindow(overlayHwnd, timeoutMs = 400)
            }

            val t1 = System.nanoTime()
            val stealMs = (t1 - t0) / 1_000_000.0

            if (stealConfirmed) {
                println("[$trialNumber] FOCUS STOLEN in %.2f ms (approach: %s)".format(stealMs, stealApproach.label))
                setOverlayText(overlayFrame, "OVERLAY HAS FOCUS\n(approach: ${stealApproach.label})")
            } else {
                println("[$trialNumber] FOCUS STEAL FAILED after %.2f ms".format(stealMs))
                setOverlayText(overlayFrame, "STEAL FAILED")
                Thread.sleep(2000)
                setOverlayText(overlayFrame, "IDLE")
                return@Thread
            }

            // 4. Wait 3 seconds (simulating user interaction)
            println("[$trialNumber] Holding focus for 3 seconds...")
            Thread.sleep(3000)

            // 5. Return focus
            println("[$trialNumber] Returning focus to previous window...")
            val t2 = System.nanoTime()
            user32.SetForegroundWindow(previousHwnd)

            val returnConfirmed = pollForegroundWindow(previousHwnd, timeoutMs = 500)
            val t3 = System.nanoTime()
            val returnMs = (t3 - t2) / 1_000_000.0

            if (returnConfirmed) {
                println("[$trialNumber] FOCUS RETURNED in %.2f ms".format(returnMs))
                setOverlayText(overlayFrame, "RETURNED TO GAME")
            } else {
                println("[$trialNumber] FOCUS RETURN FAILED after %.2f ms".format(returnMs))
                setOverlayText(overlayFrame, "RETURN FAILED")
            }

            // Summary
            println("[$trialNumber] --- Summary ---")
            println("[$trialNumber]   Steal: %.2f ms, approach: %s, success: %s".format(stealMs, stealApproach.label, stealConfirmed))
            println("[$trialNumber]   Return: %.2f ms, success: %s".format(returnMs, returnConfirmed))

            Thread.sleep(1500)
            setOverlayText(overlayFrame, "IDLE — press Alt+X")
        } catch (e: Exception) {
            println("[$trialNumber] ERROR: ${e.message}")
            e.printStackTrace()
        } finally {
            focusFlowInProgress = false
        }
    }.start()
}

fun main() {
    println("=== Focus Interception PoC ===")
    println("Press Alt+X to trigger focus steal/return cycle")
    println("Press Alt+Q to quit")
    println()

    // Create overlay frame on EDT
    var overlayFrame: JFrame? = null
    SwingUtilities.invokeAndWait {
        overlayFrame = createOverlayFrame()
    }
    val frame = overlayFrame!!

    // Wait a moment for the window to be fully realized
    Thread.sleep(500)

    val overlayHwnd = getHwndForFrame(frame)
    if (overlayHwnd == null) {
        println("ERROR: Could not find overlay HWND — aborting")
        return
    }
    println("Overlay HWND: $overlayHwnd")

    // Make the overlay not steal focus initially — minimize it so the game keeps focus
    // Actually, just set the text and let the user click the game
    setOverlayText(frame, "IDLE — press Alt+X")

    // Register global key hook
    GlobalScreen.registerNativeHook()
    var trialCount = 0

    val keyListener = object : NativeKeyListener {

        override fun nativeKeyPressed(e: NativeKeyEvent) {
            if (e.modifiers.and(NativeKeyEvent.ALT_MASK) == 0) {
                // No alt pressed
                return
            }

            when (e.keyCode) {
                NativeKeyEvent.VC_X -> {
                    trialCount++
                    runFocusFlow(frame, overlayHwnd, trialCount)
                }
                NativeKeyEvent.VC_Q -> {
                    println("\nAlt+Q pressed — shutting down")
                    running = false
                }
            }
        }

        override fun nativeKeyReleased(e: NativeKeyEvent) {
        }
    }

    GlobalScreen.addNativeKeyListener(keyListener)

    println("Ready. Switch to a game window, then press Alt+X.")
    println()

    // Block main thread until quit
    while (running) {
        Thread.sleep(100)
    }

    // Cleanup
    GlobalScreen.removeNativeKeyListener(keyListener)
    GlobalScreen.unregisterNativeHook()
    SwingUtilities.invokeAndWait {
        frame.dispose()
    }
    println("Done.")
}
