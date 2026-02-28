package com.gh.om.ks.arpgmacro.app.di

import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.overlay.FocusManager
import com.gh.om.ks.arpgmacro.core.overlay.OverlayController
import com.gh.om.ks.arpgmacro.recipe.BackgroundMacroRunner
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
    fun keyboardInput(): KeyboardInput
    fun focusManager(): FocusManager
    fun overlayController(): OverlayController
    fun backgroundMacroRunner(): BackgroundMacroRunner
    val gameSubcomponentFactory: GameSubcomponent.Factory
}
