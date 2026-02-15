package com.gh.om.ks.arpgmacro.app.di

import com.gh.om.ks.arpgmacro.core.overlay.OverlayOutput
import com.gh.om.ks.arpgmacro.overlay.ComposeOverlayWindow
import dagger.Module
import dagger.Provides
import javax.inject.Singleton

@Module
class OverlayModule {
    @Provides
    @Singleton
    fun overlayOutput(impl: ComposeOverlayWindow): OverlayOutput = impl

    @Provides
    @Singleton
    fun overlayOutputImpl(): ComposeOverlayWindow = ComposeOverlayWindow()
}
