# Focus interception PoC specification

## Goal

Verify that a JVM process can reliably steal and return window focus on Windows,
with acceptable latency for the overlay UX (leader key → overlay foreground → game foreground).

This is a standalone experiment — no Dagger, no macros, no existing infrastructure.

## What we need to learn

1. Can `SetForegroundWindow` bring our window to the foreground from a JNativeHook global key callback?
2. Which workaround is needed? Options, in order of preference:
   - (a) No workaround — just `SetForegroundWindow`. Might work because JNativeHook hooks receive input events, and the system allows the process that "received the last input event" to steal focus.
   - (b) Simulated Alt keypress via `SendInput` before `SetForegroundWindow`. This is the most commonly used workaround (used by PowerToys, AutoHotkey, etc.).
   - (c) `AttachThreadInput` to the foreground thread, then `SetForegroundWindow`. Riskier (can hang if attached thread hangs).
3. Can we reliably return focus to the previous foreground window afterward?
4. What's the latency between calling `SetForegroundWindow` and `GetForegroundWindow` confirming the switch? Is it instantaneous, or is there a measurable delay?
5. Is polling `GetForegroundWindow` sufficient to confirm the switch, or should we use `WM_ACTIVATEAPP` / `WM_SETFOCUS` messages?

## PoC structure

A single Kotlin `main()` with:

### Dependencies (existing in the project)
- `com.github.kwhat:jnativehook` — global keyboard hooks
- `net.java.dev.jna:jna` + `jna-platform` — Win32 API calls

### Components

**1. A simple Swing JFrame** (the "overlay stand-in")
- Undecorated, always-on-top, small (300x200), semi-transparent background
- Shows the current state: "IDLE", "OVERLAY HAS FOCUS", "GAME HAS FOCUS"
- Starts hidden and unfocusable (like the real overlay)

**2. JNativeHook listener**
- Listens for `Alt+X` key release (the leader key)
- On detection: triggers the focus-steal flow

**3. Focus steal/return flow** (the core of what we're testing)

```
On Alt+X detected:
  1. Record previousHwnd = GetForegroundWindow()
  2. Record t0 = System.nanoTime()
  3. Try SetForegroundWindow(overlayHwnd)
     - If approach (a) fails, try (b): SendInput(Alt down+up), then SetForegroundWindow
  4. Poll GetForegroundWindow() every 1ms until it == overlayHwnd, or timeout after 500ms
  5. Record t1 = System.nanoTime()
  6. Log: "Focus stolen in ${t1-t0}ns, approach={a|b|c}"
  7. Show "OVERLAY HAS FOCUS" in the JFrame
  8. Wait 3 seconds (simulating user picking a macro)
  9. SetForegroundWindow(previousHwnd)
  10. Poll GetForegroundWindow() every 1ms until it == previousHwnd, or timeout
  11. Record t2 = System.nanoTime()
  12. Log: "Focus returned in ${t2-after_wait}ns"
  13. Show "GAME HAS FOCUS" briefly, then hide
```

**4. Logging**
- Print all timings to stdout
- Print `GetForegroundWindow()` HWND at each step
- Print success/failure of each `SetForegroundWindow` call

### JNA bindings needed

```kotlin
// From User32 (some already available via jna-platform)
fun GetForegroundWindow(): HWND?
fun SetForegroundWindow(hWnd: HWND): Boolean
fun FindWindowW(lpClassName: String?, lpWindowName: String?): HWND?

// For approach (b)
fun SendInput(nInputs: Int, pInputs: Pointer, cbSize: Int): Int

// For getting our own window's HWND from Swing
// Use: (frame as? java.awt.Window)?.let { Native.getWindowPointer(it) }
// or FindWindowW(null, "PoC Overlay") by window title
```

## Success criteria

- [x] Focus steal succeeds at least 9/10 times when triggered from a JNativeHook callback
- [x] Focus return succeeds at least 9/10 times
- [x] Steal latency (call to confirmed) is under 100ms
- [x] Return latency is under 100ms
- [x] Identify which approach (a, b, or c) is needed and document it
- [x] Verify behavior with a game-like fullscreen window as the "previous" window (e.g., a maximized borderless Swing frame, or test with an actual game if convenient)

## Results (2026-02-16, tested against POE2 borderless)

- **Approach (a)** (direct `SetForegroundWindow`): Always fails (returns `false`). Windows blocks it.
- **Approach (b)** (`SendInput` Alt down/up + `SetForegroundWindow`): 12/12 successes.
- **Approach (c)** (`AttachThreadInput`): Not needed — (b) is reliable enough.
- **Steal latency**: ~15ms
- **Return latency**: ~16ms
- **Conclusion**: Always use approach (b). JNA caveat: `INPUT` array must use `toArray(n)` for contiguous memory, not `arrayOf(INPUT(), INPUT())`.

## Non-goals

- No Compose — plain Swing is simpler for this test
- No coroutines — plain threads/sleeps are fine
- No integration with LeaderKeyDetector or OverlayOutput
- No pretty overlay rendering
