package com.om.gh.dagger.pg

import dagger.Binds
import dagger.BindsInstance
import dagger.Component
import dagger.Module
import dagger.Provides
import dagger.Subcomponent
import javax.inject.Inject
import javax.inject.Scope
import javax.inject.Singleton

/**
 * Let's try adding custom scopes.
 * Hierarchy: App -> Session -> Screen
 */
@Scope @MustBeDocumented @Retention(AnnotationRetention.RUNTIME)
annotation class SessionScope

@Scope @Retention(AnnotationRetention.RUNTIME)
annotation class ScreenScope

interface App {
    fun nextId(): Int
}

class AppImpl : App {
    private var idGen = 0
    override fun nextId(): Int {
        idGen += 1
        return idGen
    }
}

class Session {
    var id: Int? = null
}

class Screen {
    var name: String? = null
}

interface SessionManager {
    fun genId()
}

interface ScreenManager {
    fun genName()
}

@ScreenScope
class ScreenManagerImpl @Inject constructor(
    private val screen: Screen,
    private val session: Session,
    private val app: App,
) : ScreenManager {
    override fun genName() {
        val screenId = app.nextId()
        screen.name = "Session:${session.id}/Screen:$screenId"
    }
}

@SessionScope
class SessionManagerImpl @Inject constructor(
    private val session: Session,
    private val app: App,
) : SessionManager {
    override fun genId() {
        session.id = app.nextId()
    }
}

@Module
abstract class ScreenModule {
    @ScreenScope
    @Binds
    abstract fun bindsSessionManager(impl: ScreenManagerImpl): ScreenManager
}

@Module
abstract class SessionModule {

    @SessionScope
    @Binds
    abstract fun bindsSessionManager(impl: SessionManagerImpl): SessionManager
}

@ScreenScope
@Subcomponent(modules = [ScreenModule::class])
interface ScreenSubComponent {
    val screenManager: ScreenManager
    val screen: Screen

    @Subcomponent.Factory
    interface Factory {
        fun create(@BindsInstance screen: Screen): ScreenSubComponent
    }
}

@SessionScope
@Subcomponent(modules = [SessionModule::class])
interface SessionSubComponent {
    val sessionManager: SessionManager
    val session: Session

    @Subcomponent.Factory
    interface Factory {
        // Can't use @BindsInstance on parent's subcomponent factory shorthand
        fun create(@BindsInstance session: Session): SessionSubComponent
    }

    fun screenFactory(): ScreenSubComponent.Factory
}

@SessionScope
@Component(dependencies = [AppComponent::class], modules = [SessionModule::class])
interface SessionComponent {
    val sessionManager: SessionManager

    @Component.Factory
    interface Factory {
        fun create(@BindsInstance session: Session, appComponent: AppComponent): SessionComponent
    }
}

@Module
class AppModule {
    @Singleton
    @Provides
    fun provideApp(): App = AppImpl()
}

@Singleton
@Component(modules = [AppModule::class])
interface AppComponent {
    val app: App

    // Note that a (sub-)component builder or factory is also present in the recipe bag -- It can also be depended
    // on by other recipes.
    fun sessionFactory(): SessionSubComponent.Factory
}

fun main() {
    val appComponent = DaggerAppComponent
        .create()

    val sessionComponent = appComponent
        .sessionFactory()
        .create(Session())
    sessionComponent.sessionManager.genId()

    val screenComponent = sessionComponent
        .screenFactory()
        .create(Screen())

    screenComponent.screenManager.genName()
    println(screenComponent.screen.name)
}