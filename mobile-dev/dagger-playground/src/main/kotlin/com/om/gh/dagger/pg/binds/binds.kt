package com.om.gh.dagger.pg.binds

import dagger.Binds
import dagger.Component
import dagger.Module
import dagger.Provides
import javax.inject.Inject

interface B1
interface B2

class B1Impl @Inject constructor() : B1
class B2Impl @Inject constructor() : B2

@Module
abstract class BindsModule {
    companion object {
        @JvmStatic
        @Provides
        fun b1(b1: B1Impl): B1 = b1
    }

    @Binds
    abstract fun b2(b2: B2Impl): B2
}

@Component(modules = [BindsModule::class])
interface BindsComponent {
    val b1: B1
    val b2: B2
}

fun main() {
    DaggerBindsComponent
        .create()
        .b1
}