package macroapp

import dagger.Module
import dagger.Provides
import macrocore.ActiveWindowChecker
import macrocore.Clipboard
import macrocore.MouseInput
import macrocore.Clock
import macrocore.KeyboardInput
import macrocore.KeyboardOutput
import macrocore.MouseOutput
import macrocore.Screen
import javax.inject.Singleton

@Module
class PlatformModule {
    @Provides
    @Singleton
    fun clock(): Clock = RealClock()

    @Provides
    @Singleton
    fun keyboardInput(): KeyboardInput = JNativeHookKeyboardInput()

    @Provides
    @Singleton
    fun keyboardOutput(): KeyboardOutput = JNativeHookKeyboardOutput()

    @Provides
    @Singleton
    fun mouseOutput(clock: Clock): MouseOutput = JNativeHookMouseOutput(clock)

    @Provides
    @Singleton
    fun clipboard(): Clipboard = AwtClipboard()

    @Provides
    @Singleton
    fun screen(): Screen = Win32Screen()

    @Provides
    @Singleton
    fun mouseInput(): MouseInput = JNativeHookMouseInput()

    @Provides
    @Singleton
    fun activeWindowChecker(): ActiveWindowChecker = Win32ActiveWindowChecker()
}
