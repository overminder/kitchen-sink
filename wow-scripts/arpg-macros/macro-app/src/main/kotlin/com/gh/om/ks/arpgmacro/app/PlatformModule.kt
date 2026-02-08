package com.gh.om.ks.arpgmacro.app

import dagger.Module
import dagger.Provides
import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.Clipboard
import com.gh.om.ks.arpgmacro.core.MouseInput
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.GlobalMacroConfig
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.MouseOutput
import com.gh.om.ks.arpgmacro.core.Screen
import dagger.Binds
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

@Module
abstract class PlatformModuleV2 {
    @Binds
    @Singleton
    abstract fun consoleOutput(impl: KotlinConsole): ConsoleOutput

    @Binds
    @Singleton
    abstract fun macroConfig(impl: MacroConfigImpl): GlobalMacroConfig
}
