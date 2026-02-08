package com.gh.om.ks.arpgmacro.app

import dagger.Binds
import dagger.Module
import dagger.Provides
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.LeaderKeyDetector
import com.gh.om.ks.arpgmacro.core.MouseOutput
import com.gh.om.ks.arpgmacro.core.MultiRollLoop
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.PoeInteractorImpl
import javax.inject.Singleton

@Module
abstract class MacroModule {
    @Binds
    @Singleton
    abstract fun poeInteractor(impl: PoeInteractorImpl): PoeInteractor

    @Module
    companion object {
        @Provides
        @Singleton
        @JvmStatic
        fun multiRollLoop(
            interactor: PoeInteractor,
            mouse: MouseOutput,
            clock: Clock,
        ): MultiRollLoop = MultiRollLoop(interactor, mouse, clock)

        @Provides
        @Singleton
        @JvmStatic
        fun leaderKeyDetector(
            keyboardInput: KeyboardInput,
            clock: Clock,
        ): LeaderKeyDetector = LeaderKeyDetector(
            leaderKey = setOf("Alt", "X"),
            keyboardInput = keyboardInput,
            clock = clock,
        )
    }
}
