package com.gh.om.ks.arpgmacro.app.di

import com.gh.om.ks.arpgmacro.app.impl.Win32FocusManager
import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.overlay.FocusManager
import com.gh.om.ks.arpgmacro.core.overlay.OverlayController
import com.gh.om.ks.arpgmacro.overlay.ComposeOverlayWindow
import dagger.Module
import dagger.Provides
import javax.inject.Singleton

@Module
class OverlayModule {
    @Provides
    @Singleton
    fun overlayController(
        focusManager: FocusManager,
        activeWindowChecker: ActiveWindowChecker,
    ): OverlayController = ComposeOverlayWindow(
        activeWindowChecker = activeWindowChecker,
        setClickThrough = { enabled ->
            focusManager.setClickThrough(ComposeOverlayWindow.TITLE, enabled)
        },
        stealFocus = {
            focusManager.stealFocusToOverlay(ComposeOverlayWindow.TITLE)
        },
    )

    @Provides
    @Singleton
    fun focusManager(): FocusManager = Win32FocusManager()
}
