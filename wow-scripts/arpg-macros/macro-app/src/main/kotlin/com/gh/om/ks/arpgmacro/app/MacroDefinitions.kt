package com.gh.om.ks.arpgmacro.app

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.stateIn
import com.gh.om.ks.arpgmacro.core.ChaosOrAlchMapRerollProvider
import com.gh.om.ks.arpgmacro.core.ChaosRerollProvider
import com.gh.om.ks.arpgmacro.core.CheckResult
import com.gh.om.ks.arpgmacro.core.CraftRerollProvider
import com.gh.om.ks.arpgmacro.core.CurrencySlots
import com.gh.om.ks.arpgmacro.core.GlobalMacroConfig
import com.gh.om.ks.arpgmacro.core.ItemChecker
import com.gh.om.ks.arpgmacro.core.MapScorer
import com.gh.om.ks.arpgmacro.core.MapScorerImpl
import com.gh.om.ks.arpgmacro.core.MapScorerOutput
import com.gh.om.ks.arpgmacro.core.PoeInteractor
import com.gh.om.ks.arpgmacro.core.PoeItemParser
import com.gh.om.ks.arpgmacro.core.PoeRollableItem
import com.gh.om.ks.arpgmacro.core.PoeScreenConstants
import com.gh.om.ks.arpgmacro.core.ScreenPoint
import com.gh.om.ks.arpgmacro.core.ScourAlchRerollProvider
import com.gh.om.ks.arpgmacro.core.asItemChecker
import com.gh.om.ks.arpgmacro.core.fmt
import com.gh.om.ks.arpgmacro.core.generateMapReport
import com.gh.om.ks.arpgmacro.core.postAsciiString
import com.gh.om.ks.arpgmacro.core.postPressRelease
import com.gh.om.ks.arpgmacro.recipe.activeWindowFlow
import com.gh.om.ks.arpgmacro.recipe.macroEnabledFlow
import javax.inject.Inject
import kotlin.time.Duration.Companion.seconds

// -- Currency tab slot positions (2560x1440) --

val CURRENCY_TAB_SLOTS = CurrencySlots(
    transmute = ScreenPoint(62, 355),
    alt = ScreenPoint(146, 361),
    aug = ScreenPoint(302, 432),
    regal = ScreenPoint(574, 352),
    exalt = ScreenPoint(397, 359),
    scour = ScreenPoint(576, 678),
    annul = ScreenPoint(226, 360),
    chaos = ScreenPoint(730, 356),
    alch = ScreenPoint(221, 609),
    armourScrap = ScreenPoint(572, 273),
    whetstone = ScreenPoint(501, 277),
)

// -- Map scorer adapter to ItemChecker --

class MapScorerCheckResult(
    val output: MapScorerOutput,
) : CheckResult {
    override val isGood: Boolean get() = output.isGood
}

class MapScorerItemChecker(
    private val scorer: MapScorer,
) : ItemChecker<MapScorerCheckResult> {
    override fun evaluate(item: PoeRollableItem): MapScorerCheckResult {
        return MapScorerCheckResult(scorer.evaluate(item))
    }

    override fun generateReport(results: List<MapScorerCheckResult>): String {
        return generateMapReport(results.map { it.output })
    }
}

// -- Macro functions --

suspend fun mapRollingMacro(component: AppComponent) {
    val leaderKey = component.leaderKeyDetector()
    val enabled = macroEnabledFlow(
        windowChecker = component.activeWindowChecker(),
        keyboardInput = component.keyboardInput(),
    )
    leaderKey.isEnabled("11").collect { pressed ->
        if (!pressed) return@collect
        val screen = component.screen()
        val slots = PoeScreenConstants.filterOccupiedSlots(
            PoeScreenConstants.allGrids(
                start = PoeScreenConstants.firstItemInBag,
                rows = PoeScreenConstants.bagRows,
                columns = PoeScreenConstants.bagColumns,
                gridSize = PoeScreenConstants.bagGridSize,
            ),
            screen.captureScreen(),
        )
        if (slots.isEmpty()) {
            println("No items found in bag")
            return@collect
        }
        val interactor = component.poeInteractor()
        val reroll = ChaosOrAlchMapRerollProvider(
            chaos = ChaosRerollProvider(
                fuel = 500,
                interactor = interactor,
                chaosSlot = CURRENCY_TAB_SLOTS.chaos,
                scourSlot = CURRENCY_TAB_SLOTS.scour,
                alchSlot = CURRENCY_TAB_SLOTS.alch,
            ),
            alch = ScourAlchRerollProvider(
                fuel = 500,
                interactor = interactor,
                scourSlot = CURRENCY_TAB_SLOTS.scour,
                alchSlot = CURRENCY_TAB_SLOTS.alch,
            ),
        )
        val report = component.multiRollLoop().rollItems(
            checker = MapScorerItemChecker(MapScorerImpl.SCARAB_OR_MAP),
            itemsToRoll = slots,
            rerollProvider = reroll,
            shouldContinue = enabled::value,
        )
        println(report.details)
    }
}

suspend fun craftRollingMacro(component: AppComponent) {
    val leaderKey = component.leaderKeyDetector()
    val enabled = macroEnabledFlow(
        windowChecker = component.activeWindowChecker(),
        keyboardInput = component.keyboardInput(),
    )
    leaderKey.isEnabled("15").collect { pressed ->
        if (!pressed) return@collect
        val screen = component.screen()
        val slots = PoeScreenConstants.filterOccupiedSlots(
            PoeScreenConstants.allGrids(
                start = PoeScreenConstants.firstItemInBag,
                rows = PoeScreenConstants.bagRows,
                columns = 10,
                gridSize = PoeScreenConstants.bagGridSize,
            ),
            screen.captureScreen(),
        )
        if (slots.isEmpty()) {
            println("No items found in bag")
            return@collect
        }
        val dm = CraftPresets.intStackCluster4
        val reroll = CraftRerollProvider(
            fuel = 5000,
            dm = dm,
            interactor = component.poeInteractor(),
            currencySlots = CURRENCY_TAB_SLOTS,
            clock = component.clock(),
        )
        val report = component.multiRollLoop().rollItems(
            checker = dm.asItemChecker(),
            itemsToRoll = slots,
            rerollProvider = reroll,
            shouldContinue = enabled::value,
        )
        println(report.details)
    }
}

// -- Debug macros --

suspend fun printMousePosMacro(component: AppComponent) {
    val leaderKey = component.leaderKeyDetector()
    val enabled = macroEnabledFlow(
        windowChecker = component.activeWindowChecker(),
        keyboardInput = component.keyboardInput(),
    )
    val mousePosition = component.mouseInput().motionEvents()
        .stateIn(CoroutineScope(currentCoroutineContext()))

    leaderKey.isEnabled("02").collect { pressed ->
        if (!pressed || !enabled.value) return@collect
        val pos = mousePosition.value
        val color = component.screen().getPixelColor(pos)
        println("Mouse(x = ${pos.x}, y = ${pos.y}), color = $color")
        component.clock().delay(1.seconds)
    }
}

// -- Town hotkeys --

suspend fun townHotkeyMacro(
    component: AppComponent,
    windowTitle: String,
    hotkeys: Map<String, String>,
) {
    val windowFlow = component.activeWindowChecker().activeWindowFlow(setOf(windowTitle))
        .stateIn(CoroutineScope(currentCoroutineContext()))
    val keyOutput = component.keyboardOutput()

    component.keyboardInput().keyReleases().collect { key ->
        if (!windowFlow.value) return@collect
        val command = hotkeys[key] ?: return@collect
        keyOutput.postPressRelease("Enter")
        keyOutput.postAsciiString(command)
        keyOutput.postPressRelease("Enter")
    }
}

// -- Stash sorting --

suspend fun sortInStashMacro(component: AppComponent) {
    val leaderKey = component.leaderKeyDetector()
    val enabled = macroEnabledFlow(
        windowChecker = component.activeWindowChecker(),
        keyboardInput = component.keyboardInput(),
    )

    leaderKey.isEnabled("14").collect { pressed ->
        if (!pressed) return@collect
        val screen = component.screen()
        val stashSlots = PoeScreenConstants.allGrids(
            start = PoeScreenConstants.firstItemInRegularStash,
            rows = 12,
            columns = 6,
            gridSize = PoeScreenConstants.bagGridSize,
        )
        val occupiedSlots = PoeScreenConstants.filterOccupiedSlots(
            stashSlots, screen.captureScreen(),
        )
        if (occupiedSlots.isEmpty()) {
            println("No items found in stash")
            return@collect
        }
        doSortInStash(
            interactor = component.poeInteractor(),
            scorer = MapScorerImpl.SCARAB,
            shouldContinue = enabled::value,
            inputs = occupiedSlots,
        )
    }
}

private suspend fun doSortInStash(
    interactor: PoeInteractor,
    scorer: MapScorer,
    shouldContinue: () -> Boolean,
    inputs: List<ScreenPoint>,
) {
    // Phase 1: Score all items
    val scoredItems = mutableListOf<Pair<ScreenPoint, Double>>()
    for (slot in inputs) {
        if (!shouldContinue()) return
        val text = interactor.getItemDescriptionAt(slot) ?: ""
        val item = PoeItemParser.parseAsRollable(text)
        scoredItems += slot to scorer.evaluate(item).score
    }

    // Phase 2: Sort by score descending
    scoredItems.sortBy { -it.second }
    val scores = scoredItems.map { it.second.fmt() }
    val avg = scoredItems.map { it.second }.average().fmt()
    println("${scoredItems.size} maps, avg score $avg, each: $scores")

    // Phase 3: Move all items to bag (Ctrl+click)
    for ((slot, _) in scoredItems) {
        if (!shouldContinue()) return
        interactor.ctrlClick(slot)
    }

    // Phase 4: Move back from bag to stash in sorted order (Ctrl+Shift+click)
    val bagSlots = PoeScreenConstants.allGrids(
        start = PoeScreenConstants.firstItemInBag,
        rows = PoeScreenConstants.bagRows,
        columns = 10,
        gridSize = PoeScreenConstants.bagGridSize,
    ).take(inputs.size).toList()
    for (slot in bagSlots) {
        if (!shouldContinue()) return
        interactor.ctrlShiftClick(slot)
    }
}

class MacroConfigImpl @Inject constructor(): GlobalMacroConfig {
    override val stopKey: String = "F4"
}
