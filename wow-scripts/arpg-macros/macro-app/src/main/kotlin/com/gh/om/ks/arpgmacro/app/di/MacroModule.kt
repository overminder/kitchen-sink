package com.gh.om.ks.arpgmacro.app.di

import com.gh.om.ks.arpgmacro.app.CraftPresets
import com.gh.om.ks.arpgmacro.app.POE1_CURRENCY_TAB_SLOTS
import com.gh.om.ks.arpgmacro.app.overlayEntries
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.LeaderKeyDetector
import com.gh.om.ks.arpgmacro.core.arrange.PickDropSort
import com.gh.om.ks.arpgmacro.core.arrange.PickDropSortImpl
import com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMaker
import com.gh.om.ks.arpgmacro.core.craft.CraftDecisionMakerV2
import com.gh.om.ks.arpgmacro.core.craft.CurrencySlots
import com.gh.om.ks.arpgmacro.core.overlay.OverlayOutput
import dagger.Binds
import dagger.Module
import dagger.Provides
import javax.inject.Singleton

@Module
abstract class MacroModule {

    @Binds
    @Singleton
    abstract fun pickDropSort(impl: PickDropSortImpl): PickDropSort

    @Module
    companion object {

        @Provides
        @Singleton
        @JvmStatic
        fun leaderKeyDetector(
            keyboardInput: KeyboardInput,
            clock: Clock,
            overlayOutput: OverlayOutput,
        ): LeaderKeyDetector = LeaderKeyDetector(
            leaderKey = setOf("Alt", "X"),
            keyboardInput = keyboardInput,
            clock = clock,
            onLeaderActivated = {
                overlayOutput.show(overlayEntries)
            },
            onLeaderDeactivated = {
                overlayOutput.hide()
            },
        )

        @Provides
        @Singleton
        @JvmStatic
        fun currencySlots(): CurrencySlots = POE1_CURRENCY_TAB_SLOTS

        @Provides
        @Singleton
        @JvmStatic
        fun craftDecisionMaker(): CraftDecisionMaker = CraftPresets.intStackCluster4

        @Provides
        @Singleton
        @JvmStatic
        fun craftDecisionMakerV2(): CraftDecisionMakerV2 = CraftPresets.poe2Magic
    }
}