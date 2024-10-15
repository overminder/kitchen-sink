package com.gh.om.gamemacros

import com.sun.jna.*
import com.sun.jna.platform.mac.CoreFoundation.CFStringRef
import oshi.jna.platform.mac.CoreGraphics
import oshi.jna.platform.mac.CoreGraphics.CGRect
import java.lang.reflect.Method
import java.lang.reflect.Proxy
import java.nio.charset.StandardCharsets
import com.sun.jna.Structure
import com.sun.jna.platform.mac.CoreFoundation.CFDataRef
import java.awt.Color


object MacApi {
    fun getActiveWindowTitle(): String {
        val workspace = NSObject.fromClass("NSWorkspace").msg("sharedWorkspace").send()
        val app = workspace.msg("frontmostApplication").send()
        return app.msg("localizedName", RetType.S).send()
    }

    fun getPixel(
        x: Int,
        y: Int
    ): Color {
        val bound = CGRectByValue()
        bound.origin.x = (x - 1).toDouble()
        bound.origin.y = (y - 1).toDouble()
        bound.size.width = 1.0
        bound.size.height = 1.0

        val image = CG.CGWindowListCreateImage(bound)
        // Borrowed, not retained
        val provider = CG.CGImageGetDataProvider(image)
        val data = CG.CGDataProviderCopyData(provider)
        val b = data.bytePtr.getByte(0).toUByte().toInt()
        val g = data.bytePtr.getByte(1).toUByte().toInt()
        val r = data.bytePtr.getByte(2).toUByte().toInt()

        Foundation.CFRelease(image.pointer)
        Foundation.CFRelease(data.pointer)

        return Color(r, g, b)
    }

    fun test() {
        println(getPixel(640, 360))
    }
}

fun main() {
    MacApi.test()
}

class NSObject : PointerType() {
    companion object {
        fun fromClass(name: String): NSObject {
            return Foundation.objc_getClass(name)
        }
    }
}

class CGImageRef : PointerType()
class CGDataProviderRef : PointerType()

private fun NSObject.msg(msg: String) = Msg(this, msg, RetType.O)
private fun <O> NSObject.msg(msg: String, retType: RetType<O>) = Msg(this, msg, retType)

private class Msg<O>(private val receiver: NSObject, private val msg: String, private val retTy: RetType<O>) {
    fun send(vararg args: Any?): O {
        val sel = Foundation.sel_registerName(msg)
        return when (retTy) {
            RetType.I -> Foundation.objc_msgSendI(receiver, sel, *args) as O
            RetType.O -> Foundation.objc_msgSendO(receiver, sel, *args) as O
            RetType.U -> Foundation.objc_msgSendV(receiver, sel, *args) as O
            RetType.S -> {
                val cfs = CFStringRef(Foundation.objc_msgSendO(receiver, sel, *args).pointer)
                val out = cfs.stringValue()
                cfs.release()
                out as O
            }
        }
    }
}

private sealed class RetType<O> {
    data object O : RetType<NSObject>()
    data object U : RetType<Unit>()
    data object I : RetType<Int>()
    data object S : RetType<String>()
}

@Target(AnnotationTarget.FUNCTION)
@Retention(AnnotationRetention.RUNTIME)
private annotation class SymbolName(val name: String)

private object OverloadingSymbolMapper : FunctionMapper {
    override fun getFunctionName(nl: NativeLibrary, m: Method): String {
        val ann = m.getAnnotation(SymbolName::class.java) ?: return m.name
        return ann.name
    }
}

// https://stackoverflow.com/a/67432049
private interface FoundationLibrary0 : Library {
    // https://developer.apple.com/documentation/objectivec/1418952-objc_getclass?language=objc
    fun objc_getClass(className: String): NSObject

    // https://developer.apple.com/documentation/objectivec/1418557-sel_registername?language=objc
    fun sel_registerName(selectorName: String): NSObject

    // https://developer.apple.com/documentation/objectivec/1456712-objc_msgsend?language=objc
    // The return type is actually "generic". You might need to declare this function
    // multiple times with different return types if you need them.
    @SymbolName("objc_msgSend")
    fun objc_msgSendV(receiver: NSObject, selector: NSObject, vararg args: Any?)

    @SymbolName("objc_msgSend")
    fun objc_msgSendI(receiver: NSObject, selector: NSObject, vararg args: Any?): Int

    @SymbolName("objc_msgSend")
    fun objc_msgSendO(receiver: NSObject, selector: NSObject, vararg args: Any?): NSObject

    fun objc_retain(receiver: NSObject)
    fun objc_release(receiver: NSObject)

    fun CFRelease(receiver: Pointer)
    fun CFRetain(receiver: Pointer)
}

private val Foundation = Native.load(
    "Foundation",
    FoundationLibrary0::class.java,
    mapOf(
        Library.OPTION_STRING_ENCODING to StandardCharsets.UTF_8.name(),
        Library.OPTION_FUNCTION_MAPPER to OverloadingSymbolMapper,
    )
)

class CGRectByValue : CGRect(), Structure.ByValue

private interface CoreGraphics0 : Library {
    // See https://stackoverflow.com/questions/12978846/python-get-screen-pixel-value-in-os-x/13024603#13024603
    fun CGWindowListCreateImage(
        screenBounds: CGRectByValue,
        listOption: Int = kCGWindowListOptionOnScreenOnly,
        windowId: Int = kCGNullWindowID,
        imageOption: Int = kCGWindowImageDefault
    ): CGImageRef

    fun CGImageGetDataProvider(image: CGImageRef): CGDataProviderRef

    // Actually size_t
    fun CGImageGetWidth(image: CGImageRef): Int
    fun CGImageGetHeight(image: CGImageRef): Int

    fun CGDataProviderCopyData(provider: CGDataProviderRef): CFDataRef

    companion object {
        const val kCGWindowListOptionOnScreenOnly = 1
        const val kCGWindowImageDefault = 0
        const val kCGNullWindowID = 0

        val NATIVE_LIBRARY: NativeLibrary by lazy {
            (Proxy.getInvocationHandler(CG) as Library.Handler).nativeLibrary
        }
    }
}

private val CG = Native.load(
    "CoreGraphics",
    CoreGraphics0::class.java,
    mapOf(
        Library.OPTION_STRING_ENCODING to StandardCharsets.UTF_8.name(),
    )
)
