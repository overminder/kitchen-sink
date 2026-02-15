package com.gh.om.ks.arpgmacro.app.di

import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.ConsoleOutput
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.LeaderKeyDetector
import com.gh.om.ks.arpgmacro.core.MouseInput
import com.gh.om.ks.arpgmacro.core.MultiRollLoop
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.Screen
import com.gh.om.ks.arpgmacro.core.overlay.OverlayOutput
import com.gh.om.ks.arpgmacro.overlay.ComposeOverlayWindow
import com.gh.om.ks.arpgmacro.recipe.MacroDefsComponent
import dagger.Component
import javax.inject.Singleton

@Singleton
@Component(
    modules = [
        PlatformModule::class,
        PlatformModuleV2::class,
        MacroModule::class,
        GameModule::class,
        OverlayModule::class,
    ],
)
interface AppComponent {
    fun leaderKeyDetector(): LeaderKeyDetector
    fun consoleOutput(): ConsoleOutput
    fun overlayOutputImpl(): ComposeOverlayWindow
    val gameSubcomponentFactory: GameSubcomponent.Factory
}