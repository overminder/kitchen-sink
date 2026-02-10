package com.gh.om.ks.arpgmacro.app.impl

import com.sun.jna.Native
import com.sun.jna.platform.win32.WinDef
import com.sun.jna.platform.win32.User32
import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import java.util.Arrays

private object User32Extra {
    init {
        Native.register("user32")
    }

    @JvmStatic
    external fun GetWindowTextW(
        hWnd: WinDef.HWND,
        lpString: CharArray,
        nMaxCount: Int,
    ): Int
}

class Win32ActiveWindowChecker : ActiveWindowChecker {
    private val buffer = ThreadLocal.withInitial { CharArray(1024) }

    override fun isActiveWindow(anyTitles: Collection<String>): Boolean {
        val hwnd = User32.INSTANCE.GetForegroundWindow() ?: return false
        val buf = buffer.get()
        val len = User32Extra.GetWindowTextW(hwnd, buf, buf.size - 1)
        return anyTitles.any { title ->
            if (len != title.length) return@any false
            val titleChars = title.toCharArray()
            Arrays.equals(buf, 0, len, titleChars, 0, len)
        }
    }
}
