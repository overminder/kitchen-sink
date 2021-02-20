/**
 * Basics:
 * - A Module is a recipe for resolving dependencies. They contain methods typed `() -> A` or `(A) -> B`.
 *   + Composable: A module can include sub-modules. Modules themselves are unordered, which means that
 *     we don't need to order them when structuring the sub-modules.
 * - A component takes a list of module and exports a set of dependencies. It's usually defined as an
 *   interface with a bunch of getters. Each of the return type of the getter will be resolved using the
 *   dependency information from the modules. The getters can have parameters, which will also be used
 *   in dependency resolution.
 *   + Dagger will generate a component builder that takes all the modules, and builds a concrete instance
 *     of the component. Dagger will try to use modules' default no-arg ctor if possible.
 *   + Composable: A component can be composed in two ways: via component dependency or via subcomponent.
 *     * Component dependency: A depender component can depend on one or more dependee components. The
 *       depender, in additional to using its own modules, will use the dependee's public interface to
 *       resolve its dependencies.
 *     * Subcomponent: A @Subcomponent annotation marked class can act as a return type of a parent
 *       component's getter.
 */
package com.om.gh.dagger.pg

import dagger.Component
import dagger.Module
import dagger.Provides
import dagger.Subcomponent
import javax.inject.Inject
import javax.inject.Singleton

interface Cook {
    fun fry(egg: Egg): FriedEgg
}

interface Stove {
    val doneness: Int
}

object ElectronicStove : Stove {
    override val doneness: Int = 42
}

object FireStove : Stove {
    override val doneness: Int = 100
}

class Restaurant @Inject constructor(cook: Cook) {
    val eggs = List(2) { cook.fry(Egg) }
}

class FancyRestaurant constructor(cook: Cook) {
    val eggs = List(2) { cook.fry(Egg) }
}

object Egg
data class FriedEgg(val signature: String, val doneness: Int)

class TimCook @Inject constructor(private val stove: Stove): Cook {
    override fun fry(egg: Egg) = FriedEgg("Apple", stove.doneness)
}

object SimpleCook : Cook {
    override fun fry(egg: Egg) = FriedEgg("simple", 100)
}

@Module
class CookModule {
    @Provides
    fun provideCook(cook: TimCook): Cook = cook
}

// Can either be a sub-module of cook-module, or a toplevel module in cook component.
@Module
class StoveModule(private val stove: Stove) {
    @Provides
    fun provideStove() = stove
}

@Component(modules = [CookModule::class, StoveModule::class])
interface CookComponent {
    val cook: Cook
    val restaurant: Restaurant
}

@Component(modules = [CookModule::class, StoveModule::class])
interface RestaurantComponent {
    val restaurant: Restaurant
    fun subcomp(): SubcompBasedCookComponent
}

@Module
class FancyRestaurantModule() {
    @Provides
    fun provideRestaurant(cook: Cook) = FancyRestaurant(cook)
}

// A component dependency is a component, which encapsulates its modules and only exports what's
// explicitly listed in its interface.
// See https://stackoverflow.com/a/30135139 and https://stackoverflow.com/a/30062162
// for the difference between subcomponents (module inheritance) and component dependencies (encapsulation).
@Singleton
@Component(dependencies = [CookComponent::class], modules = [FancyRestaurantModule::class])
interface DepBasedCookComponent {
    val fancyRestaurant: FancyRestaurant
}

@Singleton
@Subcomponent(modules = [FancyRestaurantModule::class])
interface SubcompBasedCookComponent {
    val fancyRestaurant: FancyRestaurant
}

@Component
interface IdComp {
    fun getCook(c: Cook): Cook
}

fun main() {
    val cookComponent = DaggerCookComponent
        .builder()
        .stoveModule(StoveModule(ElectronicStove))
        .build()
    println("By default we have ${cookComponent.restaurant.eggs}")

    val fancyRestaurant = DaggerDepBasedCookComponent
        .builder()
        .cookComponent(cookComponent)
        .build()
        .fancyRestaurant
    println("By fancy we have ${fancyRestaurant.eggs}")

    val subcomp = DaggerRestaurantComponent
        .builder()
        .stoveModule(StoveModule(ElectronicStove))
        .build()
        .subcomp()
    println("By subcomp we have ${subcomp.fancyRestaurant.eggs}")

    DaggerIdComp.create().getCook(SimpleCook)
}
