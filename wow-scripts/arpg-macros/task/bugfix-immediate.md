# Bugfix: Immediate fixes for reported issues

Status: todo
Dependencies: none

## Description

Direct fixes for the 5 bugs reported in `bug.md`. Each fix targets the specific root cause with minimal changes.

## Plan

### Bug 1: BgMacroStatusTracker overlay position

**Root cause:** `ComposeOverlayWindow.start()` hardcodes `WindowPosition(32.dp, 32.dp)` (line 124). This positions all overlay modes (picker, execution status, bg status) at the top-left.

**Fix:** When the window is showing bg status (not picker, not execution status), reposition it so its bottom-left is at (315, 1212). Use a `LaunchedEffect` that updates `windowState.position` based on the current display mode, similar to how `windowState.size` is already updated.

**Key detail:** The position (315, 1212) is in screen pixels. Compose uses `dp`. On a 2560×1440 screen at 100% scaling, 1dp ≈ 1px. If the user has display scaling, we may need to account for that — confirm with user.

### Bug 2: PrintMousePosMacro doesn't print until mouse moves

**Root cause:** `MacroRunnerImpl.run()` (line 118) calls `macroDef.prepare()` immediately before `prepared.run()`. `PrintMousePosMacro.prepare()` calls `stateIn()` on the mouse motion flow, which needs at least one emission. Since prepare happens at trigger time (not startup), there's no buffered value yet.

**Fix:** `ActivationContext` already captures `cursorPosition: ScreenPoint` at leader key press time. `PrintMousePosMacro`'s `Prepared` lambda receives the context but ignores it (parameter named `_`). Simply use `context.cursorPosition` instead of `mousePosition.value`. The `stateIn()` call in `prepare()` can be removed entirely since the macro only prints once per invocation anyway.

### Bug 3: AutoFlaskMacro blocks leader key macro "6"

**Root cause:** Needs investigation. The overlay receives key events via Compose `onPreviewKeyEvent`, while AutoFlaskMacro listens via global keyboard hooks (`KeyboardInput`). These should be independent channels.

**Investigation steps:**
1. Add logging to `handleKeyEvent()` in `ComposeOverlayWindow` to confirm whether the Compose window receives the "6" key event at all.
2. Check if `focusManager.stealFocusToOverlay()` actually succeeds when AutoFlaskMacro's background coroutines are active. AutoFlaskMacro polls `activeWindowFlow` every 100ms — if it detects the overlay as "not POE", its `active()` returns false, which is correct. But check if there are any side effects (e.g. the overlay window losing focus).
3. Check if `keyboardInput.keyPresses()` in AutoFlaskMacro's inner loop (line 77) is consuming global key events in a way that prevents delivery to the Compose window.

**Likely fix:** If the global hook is consuming key events, the fix is to ensure the hook uses non-consuming event interception (e.g. `WH_KEYBOARD_LL` on Windows returns `CallNextHookEx` to not swallow events). If focus is the issue, ensure `stealFocusToOverlay` is robust against background polling.

### Bug 4: Overlay stays visible on alt-tab

**Root cause:** `ComposeOverlayWindow` line 122:
```kotlin
val isVisible = pickerVisible || runningMacroName != null || (bgStatusLines.isNotEmpty() && gameInForeground)
```
When `pickerVisible = true`, the overlay is visible regardless of `gameInForeground`. Only the bg status mode checks foreground state.

**Fix:** Monitor foreground window changes while the picker is active. When the foreground switches to a non-game, non-overlay window, auto-cancel the picker:

1. In the `LaunchedEffect` that already polls `activeWindowChecker.activeWindowFlow`, also track overlay's own window.
2. Add a new `LaunchedEffect(pickerVisible)` that, while `pickerVisible`, polls the active window. If it's neither the game nor the overlay → call `cancel()`.

Alternatively, the Coordinator could monitor this and cancel the `awaitSelection` deferred.

### Bug 5: Leader key doesn't toggle overlay

**Root cause:** `Coordinator.onLeaderKey()` line 45: `if (state != CoordinatorState.Idle) return`. When the overlay is open (`state == Open`), a second leader key press is silently ignored.

**Fix:** When `state == Open`, cancel the pending selection instead of returning:

```kotlin
suspend fun onLeaderKey() {
    if (state == CoordinatorState.Open) {
        overlayController.cancelSelection()  // new method, or reuse existing cancel path
        return
    }
    if (state == CoordinatorState.MacroRunning) return  // still ignore during execution
    // ... rest of existing logic
}
```

This requires adding a way to cancel from outside — e.g. completing the `pendingSelection` deferred with `Cancelled` from the Coordinator. `ComposeOverlayWindow` already has a `cancel()` method that does this, but it's private. Expose it via `OverlayController`.

## Acceptance Criteria

- [ ] Bug 1: Bg status overlay positioned at (315, 1212) bottom-left
- [ ] Bug 2: PrintMousePosMacro prints position immediately on activation
- [ ] Bug 3: Pressing "6" in macro overlay works regardless of AutoFlaskMacro state
- [ ] Bug 4: Overlay auto-dismisses when foreground switches to non-game window
- [ ] Bug 5: Pressing leader key while overlay is open dismisses it
- [ ] All existing tests pass
- [ ] No regressions in overlay interaction flow

## Notes

- Bug 3 needs investigation before implementation. May want to tackle it separately if root cause is complex.
- Bugs 4 and 5 are related (both about overlay dismissal) and can be implemented together.

## Review Comments

### Overall

Good plan — code references are accurate (verified against codebase), root causes are well-identified, and fixes are minimal and targeted. A few issues:

### Bug 1: Position

Fine as described. One minor note: the plan says "bottom-left point at (315, 1212)" but doesn't address how to compute the position given the overlay's dynamic height. You'd need to know the content height to place the bottom-left at a specific point. Consider whether top-left anchoring at a computed offset is simpler, or whether bottom-left anchoring is supported by Compose's `WindowPosition`.

### Bug 3: AutoFlaskMacro blocks key "6"

The plan correctly identifies this needs investigation, but the "likely fix" section is speculative. Verified: `AutoFlaskMacro` uses both `keyPresses()` and `keyStates()`. The plan speculates about `CallNextHookEx` (event consumption at the native hook level), but the more likely culprit is the `keyPresses()` collector in AutoFlaskMacro — if it's a `SharedFlow` with limited replay/buffer and the Flask macro's collector is slow, events could be dropped for other collectors. The investigation steps are good — suggest also checking whether `keyPresses()` returns a `SharedFlow` vs `Flow`, and its replay/buffer config.

Also: the recommendation says "macro systems should work independently" (bug.md line 51). The plan's investigation is necessary, but consider also checking `Coordinator.onLeaderKey()` — the double `if (state != Idle) return` check (lines 41 and 44) means if *any* state change sneaks in (e.g., AutoFlaskMacro briefly changing coordinator state), the leader key press is silently dropped. Is there a path where AutoFlaskMacro could affect coordinator state?

### Bug 4: Overlay stays visible on alt-tab

Solid fix. Aligns well with the recommendation's intention "overlays should only be visible in games." The `LaunchedEffect` approach is fine. One concern: polling `activeWindowFlow` from *both* the visibility derivation and a separate `LaunchedEffect` could lead to race conditions (visibility flickers). Consider having a single reactive source that drives both visibility and auto-cancel.

### Bug 5: Leader key toggle

Good fix, aligns directly with the recommendation. Note: `Coordinator.onLeaderKey()` has TWO guard checks (line 41 without lock, line 44 with lock). The fix needs to handle *both* — the fast path at line 41 currently returns for all non-Idle states, so the `Open → cancel` logic would never reach the mutex-protected block. The fix should change the fast path to only skip `MacroRunning`, not `Open`.

### Missing from the plan

The recommendation says "create a plan for fixing **and testing** these issues." The acceptance criteria mention "no regressions" but no specific test strategy per bug. Bugs 4 and 5 especially would benefit from described test approaches (even if they're manual test scripts), since they involve state transitions that are easy to re-break.
