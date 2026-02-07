package macroapp

import com.github.kwhat.jnativehook.GlobalScreen
import com.github.kwhat.jnativehook.keyboard.NativeKeyEvent
import macrocore.KeyboardOutput

class JNativeHookKeyboardOutput : KeyboardOutput {

    override fun postPress(keyCode: String) {
        val code = resolveKeyCode(keyCode)
        val event = NativeKeyEvent(
            NativeKeyEvent.NATIVE_KEY_PRESSED,
            0, 0, code, NativeKeyEvent.CHAR_UNDEFINED,
        )
        GlobalScreen.postNativeEvent(event)
    }

    override fun postRelease(keyCode: String) {
        val code = resolveKeyCode(keyCode)
        val event = NativeKeyEvent(
            NativeKeyEvent.NATIVE_KEY_RELEASED,
            0, 0, code, NativeKeyEvent.CHAR_UNDEFINED,
        )
        GlobalScreen.postNativeEvent(event)
    }

    companion object {
        private val keyNameToCode = mapOf(
            "Ctrl" to NativeKeyEvent.VC_CONTROL,
            "Alt" to NativeKeyEvent.VC_ALT,
            "Shift" to NativeKeyEvent.VC_SHIFT,
            "Enter" to NativeKeyEvent.VC_ENTER,
            "Escape" to NativeKeyEvent.VC_ESCAPE,
            "Tab" to NativeKeyEvent.VC_TAB,
            "Space" to NativeKeyEvent.VC_SPACE,
            "Backspace" to NativeKeyEvent.VC_BACKSPACE,
        )

        fun resolveKeyCode(name: String): Int {
            keyNameToCode[name]?.let { return it }
            // Single character: look up VC_<char> via reflection
            if (name.length == 1) {
                val c = name[0].uppercaseChar()
                val fieldName = "VC_$c"
                return try {
                    NativeKeyEvent::class.java.getField(fieldName).getInt(null)
                } catch (e: NoSuchFieldException) {
                    error("Unknown key: $name (field $fieldName not found)")
                }
            }
            error("Unknown key name: $name")
        }
    }
}
