package com.gh.om.ks.arpgmacro.app.di

import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.overlay.FocusManager
import com.gh.om.ks.arpgmacro.core.overlay.OverlayController
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
    val gameSubcomponentFactory: GameSubcomponent.Factory
}
