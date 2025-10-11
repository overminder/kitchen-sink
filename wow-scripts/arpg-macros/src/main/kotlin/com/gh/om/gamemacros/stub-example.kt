@file:OptIn(ExperimentalCoroutinesApi::class)

package com.gh.om.gamemacros

import com.gh.om.gamemacros.GmMouse.Button
import com.gh.om.gamemacros.complex.*
import com.gh.om.gamemacros.complex.PoeGraphicConstants.emptySpaceInRightSideOfBag
import com.gh.om.gamemacros.complex.PoeGraphicConstants.gridColorHasItem
import com.gh.om.gamemacros.complex.PoeRollMap.rollMapsUntilDoneEx
import com.gh.om.gamemacros.complex.PoeRollableItem.Rarity.Normal
import com.github.kwhat.jnativehook.keyboard.NativeKeyEvent
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.launch
import java.awt.Color
import java.awt.Point
import java.time.Instant
import kotlin.math.min
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds

interface GmDeps {
    val window: GmWindow
    val mouse: GmMouse
    val keyboard: GmKeyboard
    val clipboard: GmClipboard
}

interface GmWindow {
    fun getTitleOfActiveWindow(): String
    fun captureScreen(): PixelGetter
}

interface GmMouse {
    fun moveTo(xy: Point)
    fun postPress(xy: Point, button: Button)
    fun postRelease(xy: Point, button: Button)

    enum class Button {
        Left,
        Right;
    }
}

interface GmClipboard {
    fun getString(): String?
}

suspend fun GmMouse.postClick(
    point: Point,
    button: GmMouse.Button = GmMouse.Button.Left,
    delay: Duration = 16.milliseconds,
    moveFirst: Boolean = false,
) {
    if (moveFirst) {
        moveTo(point)
        safeDelayK(delay)
    }
    postPress(point, button)
    safeDelayK(delay)
    postRelease(point, button)
}

suspend fun GmMouse.postClick(
    x: Int,
    y: Int,
    button: GmMouse.Button = GmMouse.Button.Left,
    delay: Duration = 16.milliseconds,
    moveFirst: Boolean = false,
) {
    postClick(
        Point(x, y),
        button = button,
        delay = delay,
        moveFirst = moveFirst
    )
}

interface GmKeyboard {
    fun keyState(): Flow<SimpleKeyStates>
    fun postPress(keyCode: Int)
    fun postRelease(keyCode: Int)
}

suspend fun GmKeyboard.withModifierKey(
    keyCode: Int,
    inner: suspend () -> Unit,
) {
    postPress(keyCode)
    safeDelayK(30.milliseconds)
    try {
        inner()
    } finally {
        postRelease(keyCode)
        // Important to also delay here (otherwise nested call means
        // multiple releases are done at the same time, breaking poe's
        // key handling)
        safeDelayK(30.milliseconds)
    }
}

private data class History<A : Any>(val previous: A?, val current: A)

private fun <A : Any> Flow<A>.zipWithHistory(): Flow<History<A>?> {
    val initial: History<A>? = null
    return runningFold(initial) { prevHistory, newState ->
        History(prevHistory?.current, newState)
    }
}

fun GmKeyboard.keyPresses(): Flow<String> {
    return keyState().zipWithHistory().mapNotNull {
        val newlyPressed = it?.current?.pressed.orEmpty() - it?.previous?.pressed.orEmpty()
        newlyPressed.firstOrNull()
    }
}

fun GmKeyboard.keyReleases(): Flow<String> {
    return keyState().zipWithHistory().mapNotNull {
        val newlyReleased = it?.previous?.pressed.orEmpty() - it?.current?.pressed.orEmpty()
        newlyReleased.firstOrNull()
    }
}

suspend fun GmDeps.isPoeAndTriggerKeyEnabled(
    keysToDisable: Set<String> = setOf(PoeKeyMapping.pauseMacro),
): StateFlow<Boolean> {
    return combine(
        window.isPoe(), keyboard.isTriggerKeyEnabled(keysToDisable),
    ) { isPoe, enabled ->
        isPoe && enabled
    }.stateIn(currentCoroutineScope())
}

private suspend fun GmKeyboard.isTriggerKeyEnabled(
    keysToDisable: Set<String>,
): Flow<Boolean> {
    val disabledSince = keyPresses().mapNotNull {
        // Key to temporarily disable triggers
        if (it in keysToDisable) {
            // XXX This should come from the original source of the flow,
            // not during a transformation (because flow is lazy)...
            // Otherwise, this flow should be made hot to eagerly pull
            // the current time.
            Instant.now()
        } else {
            null
        }
    }.asNullable()
        .onStart { emit(null) }
        .stateIn(currentCoroutineScope())

    return disabledSince
        .sampleAndReemit(java.time.Duration.ofSeconds(1))
        .map { disabledSince ->
            val now = Instant.now()
            disabledSince == null || now.isAfter(
                disabledSince.plusSeconds(10)
            )
        }
}

private fun <A> callbackFlowAtInterval(
    sampleInterval: Duration = 100.milliseconds,
    getValue: () -> A,
): Flow<A> {
    return callbackFlow {
        val job = launch {
            while (true) {
                trySend(getValue())
                delay(sampleInterval)
            }
        }
        awaitClose {
            job.cancel()
        }
    }
}

suspend fun GmWindow.hasActiveTitleAsState(
    title: String,
    sampleInterval: Duration = 100.milliseconds,
): StateFlow<Boolean> {
    return callbackFlowAtInterval(sampleInterval) { getTitleOfActiveWindow() == title }
        .onStart { emit(false) }
        .distinctUntilChanged()
        .stateIn(currentCoroutineScope())
}

private suspend fun GmWindow.isPoe() = hasActiveTitleAsState("Path of Exile")

class PoeRollMapWithDeps(val deps: GmDeps) {
    suspend fun main(isEnabled: Flow<Boolean>) {
        val isPoe = deps.isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            rollMapsUntilDoneEx(
                scorer = PoeMapScorerImpl.INVITATION,
                mapsToRoll = bagSlots().toList(),
                // rerollProvider = ChaosRerollProvider(1000),
                rerollProvider = ScourAlchRerollProviderWithDeps(deps, 1500),
                shouldContinue = isPoe::value,
            )
        }
        isEnabled.collect(::handle)
    }

    suspend fun bagSlots(): List<Point> {
        val grids = PoeGraphicConstants.allGrids(
            start = PoeGraphicConstants.firstItemInBag,
            rows = PoeDumpBag.bagRows,
            // Roll 20 maps at a time
            columns = 4,
            gridSize = PoeGraphicConstants.bagGridSize,
        )
        return PoeGraphicConstantsWithDeps(deps).safeCaptureThenFilterHasItem(grids)
    }
}

class PoeGraphicConstantsWithDeps(val deps: GmDeps) {
    suspend fun safeCaptureThenFilterHasItem(
        grids: Sequence<Point>,
        hasItem: (Color) -> Boolean = ::gridColorHasItem,
    ): List<Point> {
        deps.mouse.moveTo(emptySpaceInRightSideOfBag)
        safeDelayK(30.milliseconds)
        return filterPoints(grids, hasItem)
    }

    fun filterPoints(
        points: Sequence<Point>,
        predicate: (Color) -> Boolean = ::gridColorHasItem,
        getColor: (PixelGetter, Point) -> Color = PixelGetter::get,
    ): List<Point> {
        val pg = deps.window.captureScreen()
        return points.filter {
            val color = getColor(pg, it)
            predicate(color)
        }.toList()
    }
}

class LeaderKeyDetectorWithDeps(
    private val deps: GmDeps,
    private val leaderKey: Set<String>,
    private val gracePeriod: Duration = 1.seconds,
) {
    init {
        require(leaderKey.isNotEmpty())
    }

    fun isEnabled(command: String): Flow<Boolean> {
        require(command.isNotEmpty())

        val commandList = command.toList().map { it.toString() }
        // The idea is that a flow that keeps track of the currently pressed
        // sequence since leader key, plus a grace period at the end.
        var keySequence = mutableListOf<String>()

        val totalLength = leaderKey.size + commandList.size

        fun handleRelease(key: String): Boolean {
            keySequence += key
            if (keySequence.size >= leaderKey.size) {
                // Check if leader key is fully typed
                if (keySequence.take(leaderKey.size).toSet() == leaderKey) {
                    // Yes. Fall through.
                } else {
                    // throw first char away.
                    keySequence.removeAt(0)
                    return false
                }
            }
            // Check if rest of keys match.
            val receivedEnough = keySequence.size >= totalLength
            if (!receivedEnough) {
                return false
            }
            val found = keySequence
                .drop(leaderKey.size)
                .take(commandList.size) == commandList
            // Regardless of whether a match is found, clear the history.
            keySequence = keySequence.drop(totalLength).toMutableList()
            return found
        }
        return deps.keyboard.keyReleases().mapLatest {
            val result = handleRelease(it)
            delay(gracePeriod)
            result
        }
    }
}

class ScourAlchRerollProviderWithDeps(
    private val deps: GmDeps,
    private val fuel: Int = 100
) : RerollProvider {
    private val interactor = PoeInteractorWithDeps(deps)

    private var cachedAlcAndScourCount: Int? = null
    private var useCount = 0

    private suspend fun getAlcAndScourCount(): Int {
        cachedAlcAndScourCount?.let {
            return it
        }
        safeDelayK(30.milliseconds)
        val scourCount = interactor.getCountAt(
            PoeCurrencyTab.scour,
            PoeCurrency.KnownType.Scour
        )
        val alcCount = interactor.getCountAt(
            PoeCurrencyTab.alch,
            PoeCurrency.KnownType.Alch
        )
        println("alc = $alcCount, scour = $scourCount")
        val res = min(scourCount, alcCount)
        cachedAlcAndScourCount = res
        return res
    }

    override suspend fun hasMore(): Boolean {
        return fuel > useCount && getAlcAndScourCount() > useCount
    }

    override suspend fun applyTo(
        itemSlot: Point,
        item: PoeRollableItem,
    ) {
        require(hasMore())
        useCount += 1
        if (item.rarity != Normal) {
            // Scour first
            interactor.applyCurrencyTo(
                currency = PoeCurrencyTab.scour,
                item = itemSlot
            )
        }
        // Then alch
        interactor.applyCurrencyTo(
            currency = PoeCurrencyTab.alch,
            item = itemSlot
        )
    }
}

class PoeInteractorWithDeps(private val deps: GmDeps) {
    suspend fun withControlPressed(inner: suspend () -> Unit) {
        deps.keyboard.withModifierKey(NativeKeyEvent.VC_CONTROL, inner)
    }

    // For force move items
    suspend fun withControlShiftPressed(inner: suspend () -> Unit) {
        withControlPressed {
            deps.keyboard.withModifierKey(NativeKeyEvent.VC_SHIFT, inner)
        }
    }

    // For copying advanced item description
    suspend fun withControlAltPressed(inner: suspend () -> Unit) {
        withControlPressed {
            deps.keyboard.withModifierKey(NativeKeyEvent.VC_ALT, inner)
        }
    }

    suspend fun getDescriptionOfItemUnderMouse(): String? {
        withControlPressed {
            deps.keyboard.postPress(NativeKeyEvent.VC_C)
            safeDelayK(30.milliseconds)
            deps.keyboard.postRelease(NativeKeyEvent.VC_C)
            safeDelayK(30.milliseconds)
        }

        // Simulate that humans need 0.1s to read item stat.
        safeDelayK(100.milliseconds)
        return deps.clipboard.getString()
    }

    suspend fun getAdvancedDescriptionOfItemUnderMouse(): String? {
        withControlAltPressed {
            deps.keyboard.postPress(NativeKeyEvent.VC_C)
            safeDelayK(30.milliseconds)
            deps.keyboard.postRelease(NativeKeyEvent.VC_C)
            safeDelayK(30.milliseconds)
        }

        // Simulate that humans need 0.1s to read item stat.
        safeDelayK(100.milliseconds)
        return deps.clipboard.getString()
    }

    suspend fun getCountAt(
        point: Point,
        type: PoeCurrency.KnownType,
    ): Int {
        deps.mouse.moveTo(point)
        safeDelayK(30.milliseconds)

        val d = getDescriptionOfItemUnderMouse() ?: ""
        val currency = PoeItemParser.parse(d) as? PoeCurrency
        return if (currency?.type == type) {
            currency.stackSize
        } else {
            0
        }
    }

    suspend fun applyCurrencyTo(
        currency: Point,
        item: Point,
    ) {
        deps.mouse.postClick(
            point = currency,
            button = Button.Right,
            moveFirst = true
        )
        safeDelayK(30.milliseconds)
        deps.mouse.postClick(
            point = item,
            button = Button.Left,
            moveFirst = true
        )
        safeDelayK(30.milliseconds)
    }
}
