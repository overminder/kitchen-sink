package com.gh.om.ks.arpgmacro.app.di

import com.gh.om.ks.arpgmacro.di.GameScope
import com.gh.om.ks.arpgmacro.di.GameType
import com.gh.om.ks.arpgmacro.recipe.MacroDefsComponent
import dagger.BindsInstance
import dagger.Provides
import dagger.Subcomponent

@GameScope
@Subcomponent(modules = [GameSubcomponentModule::class])
interface GameSubcomponent {
    val gameType: GameType

    fun macroDefs(): MacroDefsComponent

    @Subcomponent.Factory
    interface Factory {
        fun create(@BindsInstance gameType: GameType): GameSubcomponent
    }
}