package com.gh.om.pl.cwai

import com.gh.om.pl.cwai.Kernel32.Companion.MEM_COMMIT
import com.gh.om.pl.cwai.Kernel32.Companion.MEM_RELEASE
import com.gh.om.pl.cwai.Kernel32.Companion.MEM_RESERVE
import com.gh.om.pl.cwai.Kernel32.Companion.PAGE_EXECUTE_READWRITE
import com.sun.jna.Library
import com.sun.jna.Native
import com.sun.jna.Platform
import com.sun.jna.Memory
import com.sun.jna.Pointer
import com.sun.jna.ptr.IntByReference
import com.sun.jna.Function
import com.sun.jna.win32.StdCallLibrary
import com.sun.jna.win32.W32APIOptions

// Minimal JNA binding to the C standard library's puts function
private interface CLib : Library {
    fun puts(s: String): Int
}

// Minimal binding to Kernel32 for VirtualProtect
private interface Kernel32 : StdCallLibrary {
    fun VirtualProtect(lpAddress: Pointer, dwSize: Long, flNewProtect: Int, lpflOldProtect: IntByReference): Boolean
    fun FlushInstructionCache(hProcess: Pointer, lpBaseAddress: Pointer, dwSize: Long): Boolean
    fun GetCurrentProcess(): Pointer
    fun VirtualAlloc(lpAddress: Pointer?, dwSize: Long, flAllocationType: Int, flProtect: Int): Pointer?
    fun VirtualFree(lpAddress: Pointer, dwSize: Long, dwFreeType: Int): Boolean

    companion object {
        const val MEM_RELEASE = 0x8000
        const val MEM_COMMIT = 0x1000
        const val MEM_RESERVE = 0x2000
        const val PAGE_EXECUTE_READWRITE = 0x40
    }
}

private val libcName: String = when {
    Platform.isWindows() -> "msvcrt"  // Default MSVCRT name that provides puts
    else -> "c"                        // libc on Unix-like systems
}

private val C: CLib = Native.load(libcName, CLib::class.java)
private val K32: Kernel32? = if (Platform.isWindows()) Native.load("kernel32", Kernel32::class.java, W32APIOptions.DEFAULT_OPTIONS) else null

fun compileAndPrintHelloFromC() {
    val k32 = K32 ?: error("Not on windows")
    compileAndPrintHelloFromCImpl(k32)
}

private fun compileAndPrintHelloFromCImpl(k32: Kernel32) {
    // Goal of this function is to JIT-emit a tiny Windows x86-64 function equivalent to: puts("hello"); return;
    // It's important to use JIT instead of calling puts directly via JNA, because we are going to use this as an example of JIT compilation.
    // Code bytes (Windows x64 calling convention):
    //   48 83 EC 28             ; sub rsp, 0x28          (shadow space + align)
    //   48 B9 <imm64 strPtr>    ; mov rcx, imm64         (puts arg)
    //   48 B8 <imm64 putsPtr>   ; mov rax, imm64         (target function)
    //   FF D0                   ; call rax
    //   48 83 C4 28             ; add rsp, 0x28
    //   C3                      ; ret
    // Then append the null-terminated string bytes right after the code.

    // Resolve puts() address from the loaded C runtime
    val putsFn = Function.getFunction(libcName, "puts")

    // Layout: [code (31 bytes)] [string bytes]
    val helloBytes = ("hello" + '\u0000').encodeToByteArray()
    val codeSize = 31
    val totalSize = codeSize + helloBytes.size

    // Allocate executable memory on Windows using VirtualAlloc to avoid DEP/CFG friction
    val base: Pointer
    var mem: Memory? = null
    if (Platform.isWindows()) {
        base = k32.VirtualAlloc(null, totalSize.toLong(), MEM_COMMIT or MEM_RESERVE, PAGE_EXECUTE_READWRITE)
            ?: throw RuntimeException("VirtualAlloc failed")
    } else {
        mem = Memory(totalSize.toLong())
        base = mem.share(0)
    }

    // Compute addresses
    val strAddr = Pointer.nativeValue(base) + codeSize
    val putsAddr = Pointer.nativeValue(putsFn)

    var off = 0L
    fun w8(v: Int) { base.setByte(off, v.toByte()); off += 1 }
    fun w64(v: Long) { base.setLong(off, v); off += 8 }

    // sub rsp, 0x28
    w8(0x48); w8(0x83); w8(0xEC); w8(0x28)
    // mov rcx, imm64
    w8(0x48); w8(0xB9); w64(strAddr)
    // mov rax, imm64
    w8(0x48); w8(0xB8); w64(putsAddr)
    // call rax
    w8(0xFF); w8(0xD0)
    // add rsp, 0x28
    w8(0x48); w8(0x83); w8(0xC4); w8(0x28)
    // ret
    w8(0xC3)

    // Write string
    base.write(codeSize.toLong(), helloBytes, 0, helloBytes.size)

    // On Windows, mark the entry as a valid CFG call target and flush I$ so JNA can indirect-call it safely
    if (Platform.isWindows()) {
        val proc = k32.GetCurrentProcess()
        // Ensure CPU sees freshly written instructions
        // Optional on x86_64 due to full d/i cache coherence
        if (!k32.FlushInstructionCache(proc, base, totalSize.toLong())) {
            throw RuntimeException("FlushInstructionCache failed")
        }
    }

    // Invoke the generated function. No arguments, returns int from puts; we ignore return.
    val fn = Function.getFunction(base)
    fn.invoke(Void.TYPE, emptyArray())

    // Free Windows allocation
    if (Platform.isWindows()) {
        k32.VirtualFree(base, 0, MEM_RELEASE)
    }
}
