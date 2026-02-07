package macroapp

import com.sun.jna.Native
import com.sun.jna.platform.win32.WinDef
import com.sun.jna.platform.win32.User32
import macrocore.ActiveWindowChecker

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

    override fun isActiveWindow(title: String): Boolean {
        val hwnd = User32.INSTANCE.GetForegroundWindow() ?: return false
        val buf = buffer.get()
        val len = User32Extra.GetWindowTextW(hwnd, buf, buf.size - 1)
        if (len != title.length) return false
        val titleChars = title.toCharArray()
        return java.util.Arrays.equals(buf, 0, len, titleChars, 0, len)
    }
}
