package macroapp

import dagger.Module
import dagger.Provides
import macrocore.Clipboard
import macrocore.Clock
import macrocore.KeyboardInput
import macrocore.KeyboardOutput
import macrocore.LeaderKeyDetector
import macrocore.MouseOutput
import macrocore.MultiRollLoop
import macrocore.PoeInteractor
import javax.inject.Singleton

@Module
class MacroModule {
    @Provides
    @Singleton
    fun poeInteractor(
        keyboard: KeyboardOutput,
        mouse: MouseOutput,
        clipboard: Clipboard,
        clock: Clock,
    ): PoeInteractor = PoeInteractor(keyboard, mouse, clipboard, clock)

    @Provides
    @Singleton
    fun multiRollLoop(
        interactor: PoeInteractor,
        mouse: MouseOutput,
        clock: Clock,
    ): MultiRollLoop = MultiRollLoop(interactor, mouse, clock)

    @Provides
    @Singleton
    fun leaderKeyDetector(
        keyboardInput: KeyboardInput,
        clock: Clock,
    ): LeaderKeyDetector = LeaderKeyDetector(
        leaderKey = setOf("Alt", "X"),
        keyboardInput = keyboardInput,
        clock = clock,
    )
}
