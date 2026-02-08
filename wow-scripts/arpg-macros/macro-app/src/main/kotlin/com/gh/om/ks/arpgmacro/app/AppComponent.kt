package com.gh.om.ks.arpgmacro.app

import dagger.Component
import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import com.gh.om.ks.arpgmacro.core.LeaderKeyDetector
import com.gh.om.ks.arpgmacro.core.MouseInput
import com.gh.om.ks.arpgmacro.core.MultiRollLoop
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.Screen
import com.gh.om.ks.arpgmacro.recipe.MacroDefsComponent
import javax.inject.Singleton

@Singleton
@Component(modules = [PlatformModule::class, PlatformModuleV2::class, MacroModule::class])
interface AppComponent {
    fun multiRollLoop(): MultiRollLoop
    fun leaderKeyDetector(): LeaderKeyDetector
    fun poeInteractor(): PoeInteractor
    fun screen(): Screen
    fun clock(): Clock
    fun activeWindowChecker(): ActiveWindowChecker
    fun keyboardInput(): KeyboardInput
    fun keyboardOutput(): KeyboardOutput
    fun mouseInput(): MouseInput
    fun macroDefs(): MacroDefsComponent
}
