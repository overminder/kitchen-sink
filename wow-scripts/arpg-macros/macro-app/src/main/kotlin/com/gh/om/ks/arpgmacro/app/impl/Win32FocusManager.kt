package com.gh.om.ks.arpgmacro.app.impl

import com.gh.om.ks.arpgmacro.core.ScreenPoint
import com.gh.om.ks.arpgmacro.core.overlay.ActivationContext
import com.gh.om.ks.arpgmacro.core.overlay.FocusManager
import com.sun.jna.Library
import com.sun.jna.Native
import com.sun.jna.platform.win32.User32
import com.sun.jna.platform.win32.WinDef.DWORD
import com.sun.jna.platform.win32.WinDef.HWND
import com.sun.jna.platform.win32.WinDef.POINT
import com.sun.jna.platform.win32.WinDef.WORD
import com.sun.jna.platform.win32.WinUser
import com.sun.jna.platform.win32.WinUser.INPUT

/**
 * JNA binding for Win32 functions not in jna-platform's User32.
 * - SetWindowDisplayAffinity: hides the window from GDI/Robot-based screen captures (Win10 2004+).
 * - GetWindowLongA / SetWindowLongA: read/write extended window styles (e.g. WS_EX_TRANSPARENT).
 */
private interface User32Ext : Library {
    fun SetWindowDisplayAffinity(hwnd: HWND, dwAffinity: Int): Boolean
    fun GetWindowLongA(hwnd: HWND, nIndex: Int): Int
    fun SetWindowLongA(hwnd: HWND, nIndex: Int, dwNewLong: Int): Int

    companion object {
        const val WDA_EXCLUDEFROMCAPTURE = 0x00000011
        const val GWL_EXSTYLE = -20
        const val WS_EX_TRANSPARENT = 0x00000020
        val INSTANCE: User32Ext = Native.load("user32", User32Ext::class.java)
    }
}

/**
 * Win32 implementation of [FocusManager].
 * Uses SendInput Alt + SetForegroundWindow to reliably steal focus,
 * as proven in the Phase 0 PoC (focus-poc.kt).
 */
class Win32FocusManager : FocusManager {
    private val user32 = User32.INSTANCE

    override fun captureActivationContext(): ActivationContext? {
        val hwnd = user32.GetForegroundWindow() ?: return null
        val titleBuf = CharArray(256)
        val len = user32.GetWindowText(hwnd, titleBuf, titleBuf.size)
        val title = String(titleBuf, 0, len)

        val cursorPoint = POINT()
        user32.GetCursorPos(cursorPoint)

        return ActivationContext(
            gameWindowHandle = hwnd,
            gameTitle = title,
            cursorPosition = ScreenPoint(cursorPoint.x, cursorPoint.y),
        )
    }

    override fun stealFocusToOverlay(overlayWindowTitle: String) {
        val hwnd = user32.FindWindow(null, overlayWindowTitle)
            ?: error("Overlay window '$overlayWindowTitle' not found")
        // SendInput Alt press/release tricks Windows into allowing SetForegroundWindow.
        // This is the standard workaround used by PowerToys, AutoHotkey, etc.
        sendAltKeyPress()
        user32.SetForegroundWindow(hwnd)
    }

    override fun returnFocusToGame(context: ActivationContext) {
        val hwnd = context.gameWindowHandle as? HWND ?: return
        user32.SetForegroundWindow(hwnd)
    }

    override fun excludeWindowFromCapture(windowTitle: String) {
        val hwnd = user32.FindWindow(null, windowTitle) ?: return
        User32Ext.INSTANCE.SetWindowDisplayAffinity(hwnd, User32Ext.WDA_EXCLUDEFROMCAPTURE)
    }

    override fun setClickThrough(windowTitle: String, enabled: Boolean) {
        val hwnd = user32.FindWindow(null, windowTitle) ?: return
        val exStyle = User32Ext.INSTANCE.GetWindowLongA(hwnd, User32Ext.GWL_EXSTYLE)
        val newStyle = if (enabled) {
            exStyle or User32Ext.WS_EX_TRANSPARENT
        } else {
            exStyle and User32Ext.WS_EX_TRANSPARENT.inv()
        }
        if (newStyle != exStyle) {
            User32Ext.INSTANCE.SetWindowLongA(hwnd, User32Ext.GWL_EXSTYLE, newStyle)
        }
    }

    private fun sendAltKeyPress() {
        @Suppress("UNCHECKED_CAST")
        val inputs = INPUT().toArray(2) as Array<INPUT>

        // Alt down
        inputs[0].type = DWORD(INPUT.INPUT_KEYBOARD.toLong())
        inputs[0].input.setType("ki")
        inputs[0].input.ki.wVk = WORD(WinUser.VK_MENU.toLong())
        inputs[0].input.ki.dwFlags = DWORD(0)

        // Alt up
        inputs[1].type = DWORD(INPUT.INPUT_KEYBOARD.toLong())
        inputs[1].input.setType("ki")
        inputs[1].input.ki.wVk = WORD(WinUser.VK_MENU.toLong())
        inputs[1].input.ki.dwFlags = DWORD(WinUser.KEYBDINPUT.KEYEVENTF_KEYUP.toLong())

        user32.SendInput(DWORD(2), inputs, inputs[0].size())
    }
}
