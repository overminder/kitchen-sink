# Issues that I found

Status: done
Dependencies: none

## Description

- What I see: BgMacroStatusTracker's overlay, when displayed on top of a game, will block mouse clicks. When the in-game cursor hovers over the overlay, the icon of the cursor becomes an ordinary windows cursor instead of the game-themed cursor icon.
- What I expect: the bg macro status overlay should not interact with mouse.

## Analysis

### Root cause

The Compose Desktop window is created with `transparent = true`, `undecorated = true`, and `focusable = pickerVisible` (`ComposeOverlayWindow.kt:117-123`). When showing the status badge (not picker), `focusable = false` prevents the window from receiving keyboard focus, but Windows still treats it as a mouse target — the window surface intercepts mouse hit-testing, which:
1. Blocks clicks from reaching the game underneath
2. Causes Windows to show its own cursor (the game cursor is only drawn when the game's window receives the WM_SETCURSOR message)

Compose Desktop's `transparent = true` sets `WS_EX_LAYERED` on the native HWND, but does **not** set `WS_EX_TRANSPARENT`. The `WS_EX_TRANSPARENT` extended style is what tells Windows to skip the window during hit-testing, making mouse events pass through to the window below.

### What needs to change

After the overlay window is realized, apply `WS_EX_TRANSPARENT` to its extended style using `GetWindowLong` / `SetWindowLong`. This must be toggled: enabled when showing click-through content (execution status, bg status), removed when showing interactive content (picker, confirmation).

## Plan

### Approach: toggle `WS_EX_TRANSPARENT` via `FocusManager`, using a cached HWND

`FocusManager` already owns Win32 window-style operations (`excludeWindowFromCapture`). Add a new method `setClickThrough(windowHandle, enabled)` that adds/removes `WS_EX_TRANSPARENT`.

**HWND lookup strategy**: The existing code uses `FindWindow(null, title)` every time it needs the overlay's HWND (`stealFocusToOverlay`, `excludeWindowFromCapture`). This is fragile — it depends on title uniqueness and re-searches on every call. Instead, resolve the HWND **once** after the Compose window is realized, cache it, and pass it directly. This mirrors what `captureActivationContext` already does for game windows (grabs HWND once, stores in `ActivationContext.gameWindowHandle`).

### Changes

1. **`FocusManager` interface** (`macro-core/.../overlay/FocusManager.kt`)
   - Add method:
     ```kotlin
     fun setClickThrough(windowHandle: Any, enabled: Boolean)
     ```
   - Also add a method to resolve and cache the overlay HWND:
     ```kotlin
     fun resolveWindowHandle(windowTitle: String): Any?
     ```

2. **`Win32FocusManager`** (`macro-app/.../impl/Win32FocusManager.kt`)
   - Add `GetWindowLongA` and `SetWindowLongA` to the existing `User32Ext` JNA interface (these aren't in jna-platform's `User32`)
   - Constants: `GWL_EXSTYLE = -20`, `WS_EX_TRANSPARENT = 0x20`
   - Implement `resolveWindowHandle`: single `FindWindow` call, returns HWND
   - Implement `setClickThrough`:
     ```kotlin
     override fun setClickThrough(windowHandle: Any, enabled: Boolean) {
         val hwnd = windowHandle as HWND
         val exStyle = User32Ext.INSTANCE.GetWindowLongA(hwnd, GWL_EXSTYLE)
         val newStyle = if (enabled) {
             exStyle or WS_EX_TRANSPARENT
         } else {
             exStyle and WS_EX_TRANSPARENT.inv()
         }
         if (newStyle != exStyle) {
             User32Ext.INSTANCE.SetWindowLongA(hwnd, GWL_EXSTYLE, newStyle)
         }
     }
     ```

3. **`ComposeOverlayWindow`** (`macro-overlay/.../overlay/ComposeOverlayWindow.kt`)
   - Accept a `setClickThrough: (Boolean) -> Unit` callback (keeps overlay decoupled from `FocusManager`)
   - In the `LaunchedEffect(Unit)` that calls `startedLatch.countDown()`, apply initial click-through
   - Add a `LaunchedEffect` keyed on `pickerVisible` that toggles click-through:
     ```kotlin
     LaunchedEffect(pickerVisible) {
         setClickThrough(!pickerVisible)
     }
     ```

4. **Wiring** (`MainV2` or `OverlayModule`)
   - After `overlayController.start()`, call `focusManager.resolveWindowHandle(overlayTitle)` once
   - Bind the callback: `{ enabled -> focusManager.setClickThrough(cachedHwnd, enabled) }`
   - Migrate existing `stealFocusToOverlay` / `excludeWindowFromCapture` to use the cached HWND too (optional follow-up, not required for this bug)

### Why `FocusManager` and not a new utility?

- `FocusManager` already owns Win32 window-style operations
- Adding one more method keeps the Win32 surface area in one place
- The overlay already interacts with `FocusManager` for focus stealing

### Why toggle rather than always-on?

The picker/confirmation views need mouse interaction (clicking macro rows, "Go now" button, flask config dropdown). `WS_EX_TRANSPARENT` must be removed before showing the picker and re-applied after.

### Edge case: execution status

The execution status badge (`▶ macroName`) is also non-interactive and should be click-through. The toggle condition is simply `!pickerVisible` — both execution status and bg status are shown when `pickerVisible == false`.

## Acceptance Criteria

- [x] Status badge and bg macro status line do not block mouse clicks
- [x] Game cursor stays as the game-themed cursor when hovering over the overlay area
- [x] Picker and confirmation views remain fully interactive (clickable, focusable)
- [x] Click-through is applied immediately after window creation (no brief flash of blocking)
- [x] No new polling threads or timers — just a `LaunchedEffect` reacting to `pickerVisible`
