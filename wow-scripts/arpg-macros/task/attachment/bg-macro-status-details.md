# Background Macro Visual Feedback — Design

## Goal

Show a compact, click-through status line on the overlay when background macros are actively pressing keys. The line summarizes recent activity so users know what's happening without blocking the game screen.

## Example output

```
flask [2, 3 x3] 00:50    triggerSkill [R] 00:50
```

- `flask [2, 3 x3]` — flask macro pressed key 2 once and key 3 three times in the recent window
- `00:50` — the macro has been "running" (had activity) for 50 seconds
- A macro disappears from the status line after ~15s of inactivity

## Components

### 1. `BgMacroEventSink` (macro-core, new interface)

Location: `macro-core/.../core/overlay/BgMacroStatus.kt`

```kotlin
/** Receives key-press events from background macros. */
interface BgMacroEventSink {
    fun onKeyPress(macroName: String, key: String)
}
```

Each background macro gets this injected and calls `onKeyPress` whenever it actually sends a key to the game. This is the only change needed in macro classes.

### 2. `BgMacroStatusTracker` (macro-core, new class)

Location: same file or alongside

Responsibility:
- Collects events from the sink
- Maintains a sliding window (configurable, default 15s)
- Computes and exposes `StateFlow<List<BgMacroStatusLine>>`

```kotlin
data class BgMacroStatusLine(
    val macroName: String,
    val keyCounts: List<Pair<String, Int>>,  // ordered by first-seen
    val runningDurationSecs: Long,
)

class BgMacroStatusTracker(private val clock: Clock) : BgMacroEventSink {
    private val recentWindowMs = 15_000L

    // Thread-safe event buffer
    private val events = ConcurrentLinkedDeque<BgMacroEvent>()
    // First-seen timestamp per macro (for running duration)
    private val firstSeen = ConcurrentHashMap<String, Long>()

    private val _status = MutableStateFlow<List<BgMacroStatusLine>>(emptyList())
    val status: StateFlow<List<BgMacroStatusLine>> = _status.asStateFlow()

    override fun onKeyPress(macroName: String, key: String) {
        val now = clock.currentTimeMillis()
        events.addLast(BgMacroEvent(macroName, key, now))
        firstSeen.putIfAbsent(macroName, now)
        recompute(now)
    }

    /** Called periodically or on each event to prune old entries and recompute. */
    private fun recompute(now: Long) {
        val cutoff = now - recentWindowMs
        // Evict old events
        while (events.peekFirst()?.let { it.timestamp < cutoff } == true) {
            events.pollFirst()
        }
        // Remove firstSeen for macros with no recent events
        // ... group remaining events, compute lines, update _status
    }
}

private data class BgMacroEvent(
    val macroName: String,
    val key: String,
    val timestamp: Long,
)
```

### 3. `ReportingKeyboardOutput` (macro-core, new decorator)

A `KeyboardOutput` wrapper that intercepts `postPress` / `postPressRelease` and reports to the tracker.

```kotlin
class ReportingKeyboardOutput(
    private val macroName: String,
    private val delegate: KeyboardOutput,
    private val tracker: BgMacroStatusTracker,
) : KeyboardOutput by delegate {
    override fun postPress(key: String) {
        delegate.postPress(key)
        tracker.onKeyPress(macroName, key)
    }
    override fun postPressRelease(key: String) {
        delegate.postPressRelease(key)
        tracker.onKeyPress(macroName, key)
    }
    // postRelease is NOT reported — it's the tail end of a press, not a new action
}
```

### 4. Wiring in `BackgroundMacroRunner`

- Accept `BgMacroStatusTracker` via constructor injection
- Each macro's `run()` method gains a `keyboardOutput: KeyboardOutput` parameter (instead of using the constructor-injected one)
- `BackgroundMacroRunner.run()` creates per-macro decorated instances:

```kotlin
val flaskOutput = ReportingKeyboardOutput("flask", keyboardOutput, tracker)
val focusOutput = ReportingKeyboardOutput("focus", keyboardOutput, tracker)
// ...
launch { triggerSkillMacro.run(isEnabled, focusOutput) }
```

- Expose `tracker.status` for the overlay

This means each macro needs a small signature change: `run(isEnabled, keyboardOutput)` instead of using the DI-injected field. The constructor-injected `KeyboardOutput` becomes a default/fallback.

### 5. Overlay display

Extend `BackgroundMacroState` with:
```kotlin
val statusLines: StateFlow<List<BgMacroStatusLine>>
```

In `ComposeOverlayWindow`:
- When picker is NOT visible and there are recent status lines → show a compact row (similar to `ExecutionStatusContent`)
- Format: `macroName [key xN, key2 xM] MM:SS`
- Window size adjusts to accommodate the status text
- Click-through (non-focusable), same as execution status

### 6. Changes to each background macro

Each macro's `run()` gains a `keyboardOutput: KeyboardOutput` parameter and uses it instead of the constructor-injected field. No other changes needed — the decorator handles reporting transparently.

| Macro | Decorated name | Keys reported automatically |
|-------|---------------|---------------------------|
| `AutoFlaskMacro` | `"flask"` | Flask keys via keeper's `postPressRelease` calls |
| `TriggerSkillMacro` | `"focus"` | `R` |
| `ToggleAutoAttackMacro` | `"autoAtk"` | `W` (via `postPress`) |
| `TriggerSkillsD4Macro` | `"d4Skill"` | `2`, `3`, `4` |

Note: `AutoFlaskMacro` passes the decorated `KeyboardOutput` into the keeper/`BuffManager`, so flask key presses flow through the decorator automatically. No need to change `BuffManager.useAll()` return type.

## Tests

All in `macro-core/src/test/.../recipe/BgMacroStatusTrackerShould.kt`. Use `FakeClock` for time control.

### BgMacroStatusTracker

1. **Single event** — `onKeyPress("flask", "3")` produces one status line with `keyCounts = [("3", 1)]`
2. **Multiple keys, same macro** — "3" x3 + "2" x1 → `keyCounts = [("3", 3), ("2", 1)]` (sorted by count desc)
3. **Multiple macros** — events from "flask" and "focus" → two separate status lines
4. **Sliding window eviction** — advance clock past 15s → status becomes empty
5. **Partial eviction** — some events inside window, some outside → only recent ones counted
6. **Running duration** — first event at t=0, query at t=50s → `runningDurationSecs = 50`
7. **Running duration resets after gap** — events stop >15s, new event → duration starts from new event

### ReportingKeyboardOutput

8. **Delegates and reports** — `postPressRelease("R")` calls delegate's method AND tracker receives event
9. **postRelease does not report** — `postRelease("R")` delegates but does NOT add a tracker event

## Rendering format

Compact single-line format per macro:
```
flask [3 x3, 2] 00:50
```

Rules:
- Keys sorted by count descending, then alphabetically
- `xN` omitted when N=1 (just show the key)
- Duration as `MM:SS`
- Multiple macros separated by spaces with a thin separator

## Status line visibility

- Visible when: picker is NOT open, execution status is NOT showing, AND there are status lines
- Position: same top-left corner as execution status
- Disappears when all macros have been inactive for >15s
