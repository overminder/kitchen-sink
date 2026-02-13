package com.gh.om.ks.arpgmacro.app.di

import com.gh.om.ks.arpgmacro.app.CurrencySlotsV2Impl
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.PoeInteractorImpl
import com.gh.om.ks.arpgmacro.core.craft.CurrencySlotsV2
import dagger.Binds
import dagger.Module

@Module(subcomponents = [GameSubcomponent::class])
abstract class GameModule

@Module
abstract class GameSubcomponentModule {
    @Binds
    abstract fun currencySlotsV2(impl: CurrencySlotsV2Impl): CurrencySlotsV2

    @Binds
    abstract fun poeInteractor(impl: PoeInteractorImpl): PoeInteractor
}
