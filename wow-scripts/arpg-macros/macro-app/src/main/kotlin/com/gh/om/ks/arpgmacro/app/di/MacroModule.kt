package com.gh.om.ks.arpgmacro.app.di

import com.gh.om.ks.arpgmacro.app.CURRENCY_TAB_SLOTS
import com.gh.om.ks.arpgmacro.app.CraftPresets
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.CraftDecisionMaker
import com.gh.om.ks.arpgmacro.core.CurrencySlots
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.LeaderKeyDetector
import com.gh.om.ks.arpgmacro.core.MouseOutput
import com.gh.om.ks.arpgmacro.core.MultiRollLoop
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.PoeInteractorImpl
import dagger.Binds
import dagger.Module
import dagger.Provides
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

        @Provides
        @Singleton
        @JvmStatic
        fun currencySlots(): CurrencySlots = CURRENCY_TAB_SLOTS

        @Provides
        @Singleton
        @JvmStatic
        fun craftDecisionMaker(): CraftDecisionMaker = CraftPresets.intStackCluster4
    }
}