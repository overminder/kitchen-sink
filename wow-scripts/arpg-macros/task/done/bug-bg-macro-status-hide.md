# Issues that I found

Status: done
Dependencies: none

## Description

- What I see: BgMacroStatusTracker's overlay is displayed even when the foreground window is not any of the game that runs the background macros
- What I expect: the overlay should hide when the foreground window is not in `[macro app, game that runs the macro]`

## Analysis

### Root cause

`ComposeOverlayWindow.start()` (line 111) determines visibility with:
```kotlin
val isVisible = pickerVisible || runningMacroName != null || bgStatusLines.isNotEmpty()
```

The third condition (`bgStatusLines.isNotEmpty()`) shows the overlay whenever any background macro has recent activity — regardless of which window is in the foreground. So if I alt-tab to a browser while background macros are running, the status line floats on top of the browser.

### Why the macros themselves aren't affected

Each background macro already guards its key presses with its own `activeWindowChecker` call:
- `AutoFlaskMacro` → checks POE1
- `ToggleAutoAttackMacro` → checks POE1
- `TriggerSkillsD4Macro` → checks Diablo4
- `TriggerSkillMacro` → checks POE1 (currently disabled)

So the macros stop pressing keys when the game loses focus. But `BgMacroStatusTracker` has a 15-second sliding window, meaning `bgStatusLines` remains non-empty for up to 15s after the game loses focus — keeping the overlay visible.

### What needs to change

The overlay needs its own foreground-window check: show `bgStatusLines` only when a game window (or the macro app's own overlay) is in the foreground.

## Plan

### Approach: poll `ActiveWindowChecker` in the overlay's Compose loop

The overlay already runs a Compose `application` loop on a daemon thread. Add a `LaunchedEffect` that polls `ActiveWindowChecker` (same polling approach all background macros use via `activeWindowFlow`) and exposes a `gameWindowActive` state. Gate the `bgStatusLines` visibility on this state.

### Which windows count as "active"?

The set of all game titles that have background macros. Currently:
- `"Path of Exile"` (POE1) — flask, autoAttack, triggerSkill
- `"Diablo IV"` — D4 skills

Plus the overlay's own title (`"OMKSM Overlay"`) — when the picker is shown (but this is already handled by `pickerVisible`).

### Changes

1. **`ComposeOverlayWindow`** — accept `ActiveWindowChecker` as a constructor parameter
   - Add a `LaunchedEffect` that polls `activeWindowChecker.activeWindowFlow(allBgGameTitles)` and writes to a `gameInForeground: Boolean` Compose state
   - Change the visibility condition to:
     ```kotlin
     val isVisible = pickerVisible || runningMacroName != null ||
                     (bgStatusLines.isNotEmpty() && gameInForeground)
     ```
   - Also gate the `BgMacroStatusContent` rendering on `gameInForeground`

2. **`BackgroundMacroState`** — add `gameTitles: Set<String>` field
   - The set of game window titles that background macros target
   - Populated in `MainV2` when wiring the `BackgroundMacroState`

3. **Wiring in `MainV2`** — pass the game titles set
   - Collect from the background macros: `{"Path of Exile", "Diablo IV"}`
   - Could hardcode or derive from `GameType.entries.map { GameTitles.from(it) }`

### Why not poll from `BackgroundMacroRunner` instead?

Each macro already has its own `activeWindowFlow`. We could expose a combined "any game active" flow from `BackgroundMacroRunner`. But this couples the runner to the overlay's visibility concern. The simpler approach is to let the overlay do its own independent poll — it's just a 100ms `isActiveWindow` check, same as what each macro already does.

### Alternative considered: filter at `BgMacroStatusTracker` level

Could make `BgMacroStatusTracker` stop collecting events when no game is focused. Rejected because:
- The tracker is in `macro-core` and shouldn't depend on `ActiveWindowChecker`
- The 15s window is useful — if you alt-tab briefly and come back, you still see the status
- The overlay is the right place to decide visibility

## Acceptance Criteria

- [x] Status line overlay hides within ~100ms of switching away from a game window
- [x] Status line reappears when switching back to a game window (even if mid-15s window)
- [x] Picker and execution status are unaffected (still show regardless of foreground window)
- [x] No new polling threads — reuse existing Compose coroutine scope