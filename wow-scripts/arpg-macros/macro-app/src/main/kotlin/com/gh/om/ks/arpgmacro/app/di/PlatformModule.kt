package com.gh.om.ks.arpgmacro.app.di

import com.gh.om.ks.arpgmacro.app.MacroConfigImpl
import com.gh.om.ks.arpgmacro.app.impl.RealClock
import com.gh.om.ks.arpgmacro.app.impl.Win32ActiveWindowChecker
import com.gh.om.ks.arpgmacro.app.impl.Win32Screen
import com.gh.om.ks.arpgmacro.app.impl.AwtClipboard
import com.gh.om.ks.arpgmacro.app.impl.JNativeHookKeyboardInput
import com.gh.om.ks.arpgmacro.app.impl.JNativeHookKeyboardOutput
import com.gh.om.ks.arpgmacro.app.impl.JNativeHookMouseInput
import com.gh.om.ks.arpgmacro.app.impl.JNativeHookMouseOutput
import com.gh.om.ks.arpgmacro.app.impl.KotlinConsole
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
