package com.om.gh.dagger.pg.binds

import dagger.BindsInstance
import dagger.Component
import dagger.Module
import dagger.Provides

data class Bar(val foo: Foo)
data class Bar2(val foo: Foo, val foo2: Foo2)
object Foo
object Foo2

@Module
class FooModule {
    @Provides
    fun bar(foo: Foo): Bar = Bar(foo)

    @Provides
    fun bar2(foo: Foo, foo2: Foo2): Bar2 = Bar2(foo, foo2)
}

@Component(modules = [FooModule::class])
interface FooComponent {
    val bar: Bar

    @Component.Builder
    interface Builder {
        // Equivalent to add foo to FooModule's ctor, and providing FooModule
        // to the component builder at component init time.
        fun foo(@BindsInstance foo: Foo): Builder
        fun build(): FooComponent
    }
}

@Component(modules = [FooModule::class])
interface FooComponent2 {
    val bar: Bar2

    @Component.Factory
    interface Factory {
        // Also equivalent to providing both as additional argless recipes
        fun create(@BindsInstance foo: Foo, @BindsInstance foo2: Foo2): FooComponent2
    }
}

fun main() {
    val foo = DaggerFooComponent
        .builder()
        .foo(Foo)
        .build()
        .bar
        .foo

    DaggerFooComponent2
        .factory()
        .create(Foo, Foo2)
        .bar
        .foo
}