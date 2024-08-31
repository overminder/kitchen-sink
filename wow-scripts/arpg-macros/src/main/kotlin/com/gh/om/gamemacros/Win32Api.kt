package org.example.com.gh.om.gamemacros

import com.sun.jna.Native
import com.sun.jna.platform.win32.WinDef
import com.sun.jna.platform.win32.WinDef.HDC
import com.sun.jna.platform.win32.User32 as JnaUser32Ctor

private val JnaUser32 = JnaUser32Ctor.INSTANCE

object Win32Api {
    fun getActiveWindowTitleB(buffer: CharArray): Int? {
        // During task switch, there can be no foreground window.
        val foregroundWindow = JnaUser32.GetForegroundWindow() ?: return null
        return User32.GetWindowTextW(
            hWnd = foregroundWindow,
            lpString = buffer,
            nMaxCount = buffer.size - 1
        )
    }

    fun getPixel(
        x: Int,
        y: Int
    ): Int? {
        // AHK calls GetDC(null) in PixelGetColor, so I'm following that.
        val dc = JnaUser32.GetDC(null) ?: return null
        try {
            return Gdi32.GetPixel(dc, x, y)
        } finally {
            JnaUser32.ReleaseDC(null, dc)
        }
    }
}

// Below are from https://stackoverflow.com/a/6393901

private object User32 {
    init {
        Native.register("user32")
    }

    external fun GetWindowTextW(
        hWnd: WinDef.HWND,
        lpString: CharArray,
        nMaxCount: Int
    ): Int

}

private object Gdi32 {
    init {
        Native.register("gdi32")
    }

    external fun GetPixel(
        hdc: HDC,
        x: Int,
        y: Int
    ): Int
}
