package org.example.com.gh.om.gamemacros

import com.sun.jna.Native
import com.sun.jna.Pointer
import com.sun.jna.platform.win32.WinDef
import com.sun.jna.ptr.PointerByReference

private const val MAX_TITLE_LENGTH = 1024

fun getActiveWindowTitleB(buffer: CharArray): Int {
    return User32DLL.GetWindowTextW(User32DLL.GetForegroundWindow(), buffer, buffer.size - 1)
}

fun getActiveWindowTitle(): String {
    val buffer = CharArray(MAX_TITLE_LENGTH + 1)
    getActiveWindowTitleB(buffer)
    return Native.toString(buffer)
}

private object Psapi {
    init {
        Native.register("psapi")
    }

    external fun GetModuleBaseNameW(
        hProcess: Pointer,
        hmodule: Pointer,
        lpBaseName: CharArray,
        size: Int
    ): Int
}

private object Kernel32 {
    init {
        Native.register("kernel32")
    }

    var PROCESS_QUERY_INFORMATION: Int = 0x0400
    var PROCESS_VM_READ: Int = 0x0010
    external fun GetLastError(): Int
    external fun OpenProcess(
        dwDesiredAccess: Int,
        bInheritHandle: Boolean,
        pointer: Pointer
    ): Pointer?
}

private object User32DLL {
    init {
        Native.register("user32")
    }

    external fun GetWindowThreadProcessId(
        hWnd: WinDef.HWND,
        pref: PointerByReference
    ): Int

    external fun GetForegroundWindow(): WinDef.HWND
    external fun GetWindowTextW(
        hWnd: WinDef.HWND,
        lpString: CharArray,
        nMaxCount: Int
    ): Int
}
