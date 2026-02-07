# Attachment for: ../more-macros.md

Port three macros from old codebase into macro-app/macro-core.

## Step 1: Add `KeyboardOutput` extension functions to macro-core

**`macro-core/.../KeyboardOutputExt.kt`** — New file with extensions:
```kotlin
fun KeyboardOutput.postPressRelease(key: String) {
    postPress(key)
    postRelease(key)
}

fun KeyboardOutput.postAsciiString(string: String) {
    for (c in string) {
        postPressRelease(c.toString())
    }
}
```

These compose existing `postPress`/`postRelease` — no new platform code needed. Used by townHotkey to type chat commands.

## Step 2: Add `JNativeHookMouseInput` to macro-app

**New file: `macro-app/.../JNativeHookMouseInput.kt`**

Implements `MouseInput` using JNativeHook's `NativeMouseListener` and `NativeMouseMotionListener`. Same pattern as `JNativeHookKeyboardInput` (callbackFlow + GlobalScreen listener).

```kotlin
class JNativeHookMouseInput : MouseInput {
    override fun clickEvents(): Flow<ScreenPoint> = callbackFlow {
        val listener = object : NativeMouseListener {
            override fun nativeMouseClicked(e: NativeMouseEvent) {
                trySend(ScreenPoint(e.point.x, e.point.y))
            }
        }
        GlobalScreen.addNativeMouseListener(listener)
        awaitClose { GlobalScreen.removeNativeMouseListener(listener) }
    }

    override fun motionEvents(): Flow<ScreenPoint> = callbackFlow {
        val listener = object : NativeMouseMotionListener {
            override fun nativeMouseMoved(e: NativeMouseEvent) {
                trySend(ScreenPoint(e.point.x, e.point.y))
            }
        }
        GlobalScreen.addNativeMouseMotionListener(listener)
        awaitClose { GlobalScreen.removeNativeMouseMotionListener(listener) }
    }
}
```

**`macro-app/.../PlatformModule.kt`** — Add provider:
```kotlin
@Provides @Singleton
fun mouseInput(): MouseInput = JNativeHookMouseInput()
```

**`macro-app/.../AppComponent.kt`** — Add getter:
```kotlin
fun mouseInput(): MouseInput
```

## Step 3: `printMousePos` macro

**`macro-app/.../MacroDefinitions.kt`** — Add:
```kotlin
suspend fun printMousePosMacro(component: AppComponent) {
    val leaderKey = component.leaderKeyDetector()
    val enabled = macroEnabledFlow(
        windowChecker = component.activeWindowChecker(),
        keyboardInput = component.keyboardInput(),
    )
    val mousePosition = component.mouseInput().motionEvents()
        .map { it }
        .stateIn(CoroutineScope(currentCoroutineContext()))

    leaderKey.isEnabled("02").collect { pressed ->
        if (!pressed || !enabled.value) return@collect
        val pos = mousePosition.value
        val color = component.screen().getPixelColor(pos)
        println("Mouse(x = ${pos.x}, y = ${pos.y}), color = $color")
        component.clock().delay(1.seconds)
    }
}
```

Simple — reads latest mouse position from a StateFlow, gets pixel color, prints. No average color helpers.

## Step 4: `townHotkey` macro

**`macro-app/.../MacroDefinitions.kt`** — Add:
```kotlin
suspend fun townHotkeyMacro(
    component: AppComponent,
    windowTitle: String,
    hotkeys: Map<String, String>,
) {
    val windowChecker = component.activeWindowChecker()
    val keyboard = component.keyboardInput()
    val keyOutput = component.keyboardOutput()

    // Just check window active, no F4 needed (this isn't a long-running loop)
    val windowFlow = windowChecker.activeWindowFlow(windowTitle)
        .stateIn(CoroutineScope(currentCoroutineContext()))

    keyboard.keyReleases().collect { key ->
        if (!windowFlow.value) return@collect
        val command = hotkeys[key] ?: return@collect
        keyOutput.postPressRelease("Enter")
        keyOutput.postAsciiString(command)
        keyOutput.postPressRelease("Enter")
    }
}
```

Note: this uses `keyReleases()` (not `keyPresses()`), and does NOT use leader key — it's a global hotkey listener. Only checks window active, not F4 (there's no long-running loop to cancel).

**Requires:** `keyboardOutput()` exposed on `AppComponent` (already provided by PlatformModule but not on the interface).

**`macro-app/.../AppComponent.kt`** — Add:
```kotlin
fun keyboardOutput(): KeyboardOutput
```

## Step 5: `sortInStash` macro

**`macro-app/.../MacroDefinitions.kt`** — Add:
```kotlin
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
            component = component,
            scorer = MapScorerImpl.SCARAB,
            shouldContinue = enabled::value,
            inputs = occupiedSlots,
        )
    }
}

private suspend fun doSortInStash(
    component: AppComponent,
    scorer: MapScorer,
    shouldContinue: () -> Boolean,
    inputs: List<ScreenPoint>,
) {
    val interactor = component.poeInteractor()
    val mouse = component.mouseOutput()
    val clock = component.clock()

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
```

Note: uses `PoeInteractor.ctrlClick` and `ctrlShiftClick` which already exist in macro-core. The `mouseOutput()` getter needs to be added back to AppComponent (we removed it in macro-app-cleanup but sortInStash needs it for `doSortInStash`).

**Wait** — actually `doSortInStash` only needs `PoeInteractor` (which has `getItemDescriptionAt`, `ctrlClick`, `ctrlShiftClick`). It does NOT need raw `MouseOutput` directly. So no need to re-add `mouseOutput()`.

Also needs `fmt()` — check if that's available in macro-core.

## Step 6: Wire in Main.kt

**`macro-app/.../Main.kt`** — Add to the jobs list:
```kotlin
async { printMousePosMacro(component) },
async { townHotkeyMacro(component, "Path of Exile", mapOf(
    "F5" to "/hideout",
    "F6" to "/kingsmarch",
    "F7" to "/heist",
)) },
async { townHotkeyMacro(component, "Path of Exile 2", mapOf(
    "F5" to "/hideout",
)) },
async { sortInStashMacro(component) },
```

Update the startup prints:
```kotlin
println("Launching macros (Alt+X leader key, F4 to stop)")
println("  Mouse pos:      Alt+X, 0, 2")
println("  Map rolling:    Alt+X, 1, 1")
println("  Sort in stash:  Alt+X, 1, 4")
println("  Craft rolling:  Alt+X, 1, 5")
println("  Town hotkeys:   F5=hideout, F6=kingsmarch, F7=heist (POE/POE2)")
```

## Step 7: Check `fmt()` availability

The old code uses `Number.fmt()` for formatting doubles. Check if macro-core has this. If not, add:
```kotlin
// macro-core utils
fun Double.fmt(): String = String.format("%.2f", this)
```

## Files Summary

| File | Action |
|------|--------|
| `macro-core/.../KeyboardOutputExt.kt` | New — `postPressRelease`, `postAsciiString` extensions |
| `macro-core/.../Platform.kt` | No changes needed (MouseInput already defined) |
| `macro-app/.../JNativeHookMouseInput.kt` | New — MouseInput impl |
| `macro-app/.../PlatformModule.kt` | Add `mouseInput()` provider |
| `macro-app/.../AppComponent.kt` | Add `mouseInput()`, `keyboardOutput()` getters |
| `macro-app/.../MacroDefinitions.kt` | Add `printMousePosMacro`, `townHotkeyMacro`, `sortInStashMacro`, `doSortInStash` |
| `macro-app/.../Main.kt` | Wire all new macros, update startup prints |

## Verification

1. `./gradlew :macro-core:test` — existing tests still pass
2. `./gradlew :macro-app:build` — compiles with all changes
3. `get_file_problems` on all changed files — zero errors
