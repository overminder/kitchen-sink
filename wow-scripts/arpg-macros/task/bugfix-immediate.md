# Bugfix: Immediate fixes for reported issues

Status: todo
Dependencies: none

## Description

Direct fixes for the 5 bugs reported in `bug.md`. Each fix targets the specific root cause with minimal changes.

## Plan

### Bug 1: BgMacroStatusTracker overlay position

**Root cause:** `ComposeOverlayWindow.start()` hardcodes `WindowPosition(32.dp, 32.dp)` (line 124). This positions all overlay modes (picker, execution status, bg status) at the top-left.

**Fix:** Extend the existing `LaunchedEffect` that updates `windowState.size` (keyed on `pickerVisible, runningMacroName, bgStatusLines.isNotEmpty()`) to also update `windowState.position`. Bg status size is fixed at `BG_STATUS_SIZE = DpSize(480.dp, 36.dp)`, so the top-left position for bottom-left anchoring at (315, 1212) is:

```kotlin
windowState.position = WindowPosition(
    x = 315.dp,
    y = (1212 - 36).dp,  // 1176.dp — bottom-left (315, 1212) minus height
)
```

For picker and execution status modes, keep the existing `(32.dp, 32.dp)` position. Compute position alongside size in the same `LaunchedEffect`:

```kotlin
LaunchedEffect(pickerVisible, runningMacroName, bgStatusLines.isNotEmpty()) {
    windowState.size = computeWindowSize(pickerVisible, runningMacroName != null, bgStatusLines.isNotEmpty())
    windowState.position = when {
        pickerVisible || runningMacroName != null -> WindowPosition(32.dp, 32.dp)
        bgStatusLines.isNotEmpty() -> WindowPosition(315.dp, (1212 - 36).dp)
        else -> windowState.position  // no change
    }
}
```

**Files:** `macro-overlay/.../ComposeOverlayWindow.kt` — one `LaunchedEffect` block, ~3 lines added.

### Bug 2: PrintMousePosMacro doesn't print until mouse moves

**Root cause:** `PrintMousePosMacro.prepare()` calls `mouseInput.motionEvents().stateIn(scope)` which creates a `StateFlow` from a cold `callbackFlow`. The `StateFlow` has no initial value from the mouse motion flow — `stateIn` requires an initial emission or an explicit `initialValue`. Since `prepare()` runs at trigger time, the mouse hasn't moved yet, so `mousePosition.value` blocks or returns a stale/default value.

**Fix:** In `PrintMousePosMacro`:

1. Remove the `stateIn()` call and the `mousePosition` variable from `prepare()`.
2. Rename the `_` parameter in the `Prepared` lambda to `context`.
3. Use `context.cursorPosition` instead of `mousePosition.value`.

Before:
```kotlin
override suspend fun prepare(): MacroDef.Prepared {
    val mousePosition = mouseInput.motionEvents()
        .stateIn(CoroutineScope(currentCoroutineContext()))
    val shouldContinue = shouldContinueChecker.get(anyWindowTitles = GameTitles.ALL_POE)
    return MacroDef.Prepared { _ ->
        if (!shouldContinue.value) return@Prepared
        val pos = mousePosition.value
        val color = screen.getPixelColor(pos)
        consoleOutput.println("Mouse(x = ${pos.x}, y = ${pos.y}), color = $color")
        clock.delay(1.seconds)
    }
}
```

After:
```kotlin
override suspend fun prepare(): MacroDef.Prepared {
    val shouldContinue = shouldContinueChecker.get(anyWindowTitles = GameTitles.ALL_POE)
    return MacroDef.Prepared { context ->
        if (!shouldContinue.value) return@Prepared
        val pos = context.cursorPosition
        val color = screen.getPixelColor(pos)
        consoleOutput.println("Mouse(x = ${pos.x}, y = ${pos.y}), color = $color")
        clock.delay(1.seconds)
    }
}
```

The `mouseInput` constructor dependency can also be removed since it's no longer used. Check if any other method in the class uses it first.

**Files:** `macro-core/.../recipe/PrintMousePosMacro.kt` — remove 2 lines, rename 1 parameter, change 1 reference.

### Bug 3: AutoFlaskMacro blocks leader key macro "6"

**Root cause:** Investigation complete — speculative causes eliminated:

- **Not event consumption:** `JNativeHookKeyboardInput` uses jnativehook's `GlobalScreen.addNativeKeyListener()`, which is a passive observer. Events are not swallowed; multiple listeners each get their own callback.
- **Not SharedFlow buffer contention:** `keyPresses()` returns a cold `callbackFlow` — each `collect` call creates a new independent listener. No shared buffer.
- **Not Coordinator state interference:** `AutoFlaskMacro` has no dependency on `Coordinator` or `CoordinatorState`. It cannot change coordinator state.

**Remaining hypothesis — focus stealing race:** `AutoFlaskMacro` polls `activeWindowFlow` every 100ms via `stateIn()`. When the overlay opens, `Coordinator.onLeaderKey()` calls `focusManager.stealFocusToOverlay()`. The overlay becomes the active window. The Compose window receives key events via `onPreviewKeyEvent`, which requires the window to have OS-level focus. If `AutoFlaskMacro`'s `active()` check triggers a side effect (e.g., re-focusing the game window) while the overlay is showing, the overlay loses focus and stops receiving key events.

**Investigation step (runtime):** Add temporary logging to `ComposeOverlayWindow.handleKeyEvent()` to confirm whether the "6" `KeyEvent` arrives at all when AutoFlaskMacro is active. This determines if the issue is focus-related (event never arrives) or handling-related (event arrives but is misprocessed).

**Planned fix (pending investigation):** If focus loss is confirmed, ensure `AutoFlaskMacro.active()` returns `false` when the overlay is visible (it already should — the overlay window title is not in `GameTitles.POE1`). Check `stealFocusToOverlay` for races with the 100ms polling interval. May need to add a brief delay or a "focus lock" flag that prevents background macros from interfering during overlay display.

**Files:** TBD after investigation. Likely `macro-overlay/.../ComposeOverlayWindow.kt` (logging) and possibly `macro-core/.../recipe/AutoFlaskMacro.kt`.

### Bug 4: Overlay stays visible on alt-tab

**Root cause:** `ComposeOverlayWindow` visibility logic:
```kotlin
val isVisible = pickerVisible || runningMacroName != null || (bgStatusLines.isNotEmpty() && gameInForeground)
```
`pickerVisible` is not gated on `gameInForeground`, so the picker stays visible when alt-tabbing away from the game.

**Fix:** Add a `LaunchedEffect` in `ComposeOverlayWindow.start()` that auto-cancels the picker when the foreground window is neither the game nor the overlay. This uses the existing `activeWindowChecker` and the overlay's own window title.

Implementation in the composable body, after the existing `LaunchedEffect` block that updates size/position:

```kotlin
// Auto-cancel picker when user switches away from game
if (bgMacroState != null) {
    LaunchedEffect(pickerVisible) {
        if (!pickerVisible) return@LaunchedEffect
        activeWindowChecker.activeWindowFlow(
            bgMacroState!!.gameTitles + TITLE  // game windows + overlay window
        ).collect { isForeground ->
            if (!isForeground) cancel()
        }
    }
}
```

**Edge case — no bgMacroState:** If `bgMacroState` is null (no background macros connected), `activeWindowChecker` is still available as a constructor dependency. Use it directly with game titles from the `ActivationContext` passed to `awaitSelection`. Store the game title when `awaitSelection` is called:

```kotlin
private var currentGameTitle: String? = null

override suspend fun awaitSelection(...): OverlaySelection {
    currentGameTitle = context.gameTitle
    // ... existing code ...
}
```

Then the `LaunchedEffect` uses `setOf(currentGameTitle!!, TITLE)` instead of `bgMacroState!!.gameTitles + TITLE`.

**Why not change the `isVisible` formula:** Changing `isVisible` to include `&& gameInForeground` for picker mode would make the window invisible but not cancel the selection — the `awaitSelection` coroutine would still be suspended, and the coordinator would be stuck in `Open` state until the inactivity timeout fires. Auto-canceling is the correct approach.

**Files:** `macro-overlay/.../ComposeOverlayWindow.kt` — add one field, ~10 lines in `LaunchedEffect`.

### Bug 5: Leader key doesn't toggle overlay

**Root cause:** `Coordinator.onLeaderKey()` has two guard checks that both reject non-Idle states:

```kotlin
// Fast path (line ~41, no lock):
if (state != CoordinatorState.Idle) return

// Mutex-protected (line ~44, inside withLock):
if (state != CoordinatorState.Idle) return
```

When `state == Open`, both guards return early. The second leader key press is silently ignored.

**Fix — three changes:**

**1. Add `cancelSelection()` to `OverlayController` interface** (`macro-core/.../overlay/OverlayController.kt`):

```kotlin
interface OverlayController {
    // ... existing methods ...

    /**
     * Cancel a pending [awaitSelection] from outside the overlay.
     * No-op if no selection is pending.
     */
    fun cancelSelection()
}
```

**2. Implement in `ComposeOverlayWindow`** (`macro-overlay/.../ComposeOverlayWindow.kt`):

```kotlin
override fun cancelSelection() {
    cancel()  // delegates to existing private cancel() method
}
```

**3. Modify `Coordinator.onLeaderKey()`** (`macro-core/.../overlay/Coordinator.kt`):

Change the fast path guard to allow `Open` state through:

```kotlin
suspend fun onLeaderKey() {
    // Fast path: skip only if macro is running
    if (state == CoordinatorState.MacroRunning) return

    mutex.withLock {
        // Cancel if overlay is already open (toggle behavior)
        if (state == CoordinatorState.Open) {
            overlayController.cancelSelection()
            return
        }
        if (state != CoordinatorState.Idle) return

        // ... rest of existing logic unchanged ...
    }
}
```

**How it works:** `cancelSelection()` calls `pendingSelection?.complete(Cancelled)`, which unblocks the `deferred.await()` inside `awaitSelection()`. The `finally` block in `awaitSelection` clears `pickerVisible` and `pendingSelection`. Back in `Coordinator.onLeaderKey`, the `when (selection)` branch hits `Cancelled`, the `finally` block sets `state = Idle`.

**Thread safety:** The `cancelSelection()` call inside `mutex.withLock` is safe because `CompletableDeferred.complete()` is thread-safe and non-blocking. The original `onLeaderKey` call that is suspended on `deferred.await()` already holds a reference to the deferred but is *not* holding the mutex (it released it before `awaitSelection` was called — wait, let me re-check).

**Re-check:** Looking at the actual code, `awaitSelection` is called *inside* `mutex.withLock`. This means the first `onLeaderKey` call holds the mutex while suspended on `deferred.await()`. The second `onLeaderKey` call would block on `mutex.withLock` and never reach the `if (state == Open)` check.

**Revised fix:** Move the `Open` state check to *before* the mutex:

```kotlin
suspend fun onLeaderKey() {
    // Fast path: skip if macro is running
    if (state == CoordinatorState.MacroRunning) return

    // Toggle: cancel overlay if it's open (no lock needed — cancelSelection is thread-safe)
    if (state == CoordinatorState.Open) {
        overlayController.cancelSelection()
        return
    }

    mutex.withLock {
        if (state != CoordinatorState.Idle) return
        // ... rest unchanged ...
    }
}
```

This works because:
- `state` is read volatilely (it's checked outside the lock in the original code too)
- `CompletableDeferred.complete()` is thread-safe
- After `cancelSelection()`, the first `onLeaderKey` call resumes from `deferred.await()`, hits the `Cancelled` branch, and sets `state = Idle` in its `finally` block

**Files:** 3 files, ~5 lines each.

## Acceptance Criteria

- [x] Bug 1: Bg status overlay positioned at (315, 1212) bottom-left
- [x] Bug 2: PrintMousePosMacro prints position immediately on activation
- [ ] Bug 3: Pressing "6" in macro overlay works regardless of AutoFlaskMacro state
- [ ] Bug 4: Overlay auto-dismisses when foreground switches to non-game window
- [x] Bug 5: Pressing leader key while overlay is open dismisses it
- [ ] All existing tests pass
- [ ] No regressions in overlay interaction flow

## Notes

- Bug 3 needs runtime investigation before implementation — add logging first, then fix based on findings.
- Bugs 4 and 5 both require adding `cancelSelection()` to `OverlayController`. Implement Bug 5 first (adds the method), then Bug 4 (uses it).
- Execution order: Bug 2 → Bug 1 → Bug 5 → Bug 4 → Bug 3 (easiest/most independent first, investigation last).

## Test Strategy

- **Bug 2:** No new test needed — existing invocation paths exercise `PrintMousePosMacro`. Manual verification: trigger the macro and confirm position prints immediately.
- **Bug 4:** Add a test to `CoordinatorTest` (or create one): mock `OverlayController.awaitSelection` to suspend indefinitely, then verify that when `activeWindowFlow` emits `false`, the selection is cancelled and state returns to `Idle`.
- **Bug 5:** Add a test to `CoordinatorTest`: call `onLeaderKey()` to enter `Open` state, then call `onLeaderKey()` again concurrently and verify `cancelSelection()` is called and state returns to `Idle`.
