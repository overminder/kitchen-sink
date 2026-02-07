# Attachment for: ../macro-app-cleanup.md

Fix 4 issues found during code review of the macro-app module.

## Step 1: Remove dead `mouseOutput()` from AppComponent

**`macro-app/.../AppComponent.kt`** — Remove `fun mouseOutput(): MouseOutput` and its `MouseOutput` import.

## Step 2: Fix `MapScorerItemChecker.generateReport`

**`macro-app/.../MacroDefinitions.kt`**:
- Make `MapScorerCheckResult.output` non-private (`private val` → `val`)
- Change `generateReport` body from `return "Ok"` to `return generateMapReport(results.map { it.output })`
- Add import for `macrocore.generateMapReport`

## Step 3: Extract craft presets

**New file: `macro-app/.../CraftPresets.kt`** — Object holding named `CraftDecisionMaker` instances:
```kotlin
object CraftPresets {
    /** Int-stacking cluster jewel: 4 of 6 target mods (ES, effect, int, AS, all res, attr). */
    val intStackCluster4 = CraftDecisionMaker.byDesiredMods(
        desiredModNames = listOf("Glowing", "Powerful", "of the Prodigy",
            "of Mastery", "of the Kaleidoscope", "of the Meteor"),
        desiredModCount = 4,
    )
}
```

**`macro-app/.../MacroDefinitions.kt`** — Replace inline `CraftDecisionMaker.byDesiredMods(...)` with `CraftPresets.intStackCluster4`.

## Step 4: Add cancellation support (active window + F4 stop)

Follows the same Flow-based pattern as the old code (`isPoeAndTriggerKeyEnabled` in `GameSpecific.kt`). No explicit state management — the `shouldContinue` signal is a live `StateFlow<Boolean>` composed from two reactive sources. Each leader-key trigger starts a fresh `rollItems` call; the flow is always in the correct state by then.

### 4a. `ActiveWindowChecker` interface in macro-core

**`macro-core/.../Platform.kt`** — Add:
```kotlin
/**
 * Checks whether a given window title matches the current foreground window.
 * Low-level platform capability, like Screen or Clipboard.
 */
interface ActiveWindowChecker {
    fun isActiveWindow(title: String): Boolean
}
```

### 4b. Fake in macro-core tests

**`macro-core/.../FakePlatform.kt`** — Add:
```kotlin
class FakeActiveWindowChecker : ActiveWindowChecker {
    var activeTitle: String = ""
    override fun isActiveWindow(title: String) = activeTitle == title
}
```

### 4c. Win32 implementation

**New file: `macro-app/.../Win32ActiveWindowChecker.kt`**

Uses `User32.INSTANCE.GetForegroundWindow()` + `GetWindowTextW` (same pattern as old `Win32Api.kt` and `Win32Screen.kt`'s `Gdi32` object). ThreadLocal `CharArray(1024)` buffer.

### 4d. Flow-based cancellation utility in macro-app

**New file: `macro-app/.../MacroCancellation.kt`**

Replicates the old `isPoeAndTriggerKeyEnabled` pattern using the new macro-core interfaces:

```kotlin
/**
 * Polls ActiveWindowChecker and emits whether the given title is the foreground window.
 */
fun ActiveWindowChecker.activeWindowFlow(
    title: String,
    interval: Duration = 100.milliseconds,
): Flow<Boolean> = flow {
    while (true) {
        emit(isActiveWindow(title))
        delay(interval)
    }
}

/**
 * Emits false for [disableDuration] after any key in [keys] is pressed, true otherwise.
 * Same semantics as old isTriggerKeyEnabled().
 */
fun KeyboardInput.triggerKeyEnabledFlow(
    keys: Set<String>,
    disableDuration: Duration = 3.seconds,
    clock: Clock,
): Flow<Boolean> {
    return keyPresses()
        .filter { it in keys }
        .map { clock.currentTimeMillis() }
        .onStart { emit(0L) }  // start enabled
        .transformLatest { pressedAt ->
            if (pressedAt == 0L) {
                emit(true)  // initial state
            } else {
                emit(false)
                delay(disableDuration)
                emit(true)
            }
        }
}

/**
 * Combines active-window check and stop-key into a single StateFlow<Boolean>.
 * Read .value as shouldContinue. Same pattern as old isPoeAndTriggerKeyEnabled().
 */
suspend fun macroEnabledFlow(
    windowChecker: ActiveWindowChecker,
    keyboardInput: KeyboardInput,
    clock: Clock,
    windowTitle: String = "Path of Exile",
    stopKeys: Set<String> = setOf("F4"),
): StateFlow<Boolean> {
    return combine(
        windowChecker.activeWindowFlow(windowTitle),
        keyboardInput.triggerKeyEnabledFlow(stopKeys, clock = clock),
    ) { windowActive, keyEnabled -> windowActive && keyEnabled }
        .stateIn(currentCoroutineScope())
}
```

**Why this matches the old code:**
- `activeWindowFlow` replaces `ScreenCommons.activeWindowHas()` — polls window title on an interval
- `triggerKeyEnabledFlow` replaces `isTriggerKeyEnabled()` — disables for 3s after F4
- `macroEnabledFlow` replaces `isPoeAndTriggerKeyEnabled()` — combines both into a StateFlow
- No `reset()` needed — F4 auto-recovers after the timeout, and each leader-key trigger starts a fresh `rollItems` call that reads the current `flow.value`

### 4e. Dagger wiring

**`macro-app/.../PlatformModule.kt`** — Add provider:
```kotlin
@Provides @Singleton
fun activeWindowChecker(): ActiveWindowChecker = Win32ActiveWindowChecker()
```

**`macro-app/.../AppComponent.kt`** — Add getter:
```kotlin
fun activeWindowChecker(): ActiveWindowChecker
```

### 4f. Wire into macros

**`macro-app/.../MacroDefinitions.kt`** — Both macros build the cancellation flow at the top of the `collect` block and pass `::value` to `rollItems`:

```kotlin
suspend fun mapRollingMacro(component: AppComponent) {
    val leaderKey = component.leaderKeyDetector()
    val enabled = macroEnabledFlow(
        windowChecker = component.activeWindowChecker(),
        keyboardInput = component.keyboardInput(),
        clock = component.clock(),
    )
    leaderKey.isEnabled("11").collect { pressed ->
        if (!pressed) return@collect
        // ... existing slot detection ...
        val report = component.multiRollLoop().rollItems(
            // ...
            shouldContinue = enabled::value,
        )
        // ...
    }
}
```

Note: `macroEnabledFlow` is called once outside the collect (it's a long-lived StateFlow), not per-trigger. The flow stays active for the macro's lifetime. `enabled.value` always reflects current state.

**`macro-app/.../AppComponent.kt`** — Also expose `keyboardInput()` (already provided by `PlatformModule` but not on the component interface):
```kotlin
fun keyboardInput(): KeyboardInput
```

**`macro-app/.../Main.kt`** — Add print line about F4 stopping macros.

## Files Summary

| File | Action |
|------|--------|
| `macro-core/.../Platform.kt` | Add `ActiveWindowChecker` interface |
| `macro-core/.../FakePlatform.kt` | Add `FakeActiveWindowChecker` |
| `macro-app/.../Win32ActiveWindowChecker.kt` | New — Win32 impl |
| `macro-app/.../MacroCancellation.kt` | New — Flow-based cancellation utility |
| `macro-app/.../CraftPresets.kt` | New — named craft configs |
| `macro-app/.../PlatformModule.kt` | Add `activeWindowChecker()` provider |
| `macro-app/.../AppComponent.kt` | Remove `mouseOutput()`, add `activeWindowChecker()` + `keyboardInput()` |
| `macro-app/.../MacroDefinitions.kt` | Fix report, use presets, wire shouldContinue |
| `macro-app/.../Main.kt` | Add F4 info print |

## Verification

1. `./gradlew :macro-core:test` — existing tests still pass
2. `./gradlew :macro-app:build` — compiles with all changes
