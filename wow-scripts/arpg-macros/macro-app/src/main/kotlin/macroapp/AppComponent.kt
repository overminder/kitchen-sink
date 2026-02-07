package macroapp

import dagger.Component
import macrocore.ActiveWindowChecker
import macrocore.Clock
import macrocore.KeyboardInput
import macrocore.KeyboardOutput
import macrocore.LeaderKeyDetector
import macrocore.MouseInput
import macrocore.MultiRollLoop
import macrocore.PoeInteractor
import macrocore.Screen
import javax.inject.Singleton

@Singleton
@Component(modules = [PlatformModule::class, MacroModule::class])
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
}
