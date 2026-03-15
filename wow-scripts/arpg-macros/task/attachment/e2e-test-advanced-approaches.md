# E2E Test — Advanced Approaches

Two testing approaches that are strictly more powerful than Layer 4's handcrafted scenario replay, in terms of the class of bugs they catch.

**Related:** [observability task](../observability.md) covers production-time recording and live invariant checking. Session recordings from observability feed into simulator validation (Approach B) and can supersede Layer 4's synthetic recordings for regression testing.

## Why handcrafted scenarios hit a ceiling

All 4 layers in the current plan use **human-authored test cases**. A human thinks of a scenario (e.g., "alt-tab while picker is open"), writes a test for it, and checks specific assertions. This has two fundamental limits:

1. **Coverage is proportional to human imagination.** Rare race conditions arise from event combinations that are hard to reason about manually — e.g., "key release arrives in the 2ms window between focus steal starting and overlay becoming focusable."
2. **Static recordings can't test feedback loops.** When the system's output changes the environment (pressing flask key → game shows buff active → pixel color changes → macro detects buff → stops pressing), a static recording can't model this dynamic interaction.

---

## Approach A: Property-based testing (randomized invariant checking)

### Core idea

Generate **random sequences of input events** and check that **system invariants** always hold, regardless of the sequence. If an invariant is violated, the test framework reports the minimal reproducing sequence.

This is dramatically more powerful than handcrafted scenarios because it explores the state space that humans don't think to test.

### Architecture

Runs on the **fake platform** (Layer 0 level) for speed. Each test execution runs thousands of random sequences in seconds.

```
┌────────────────────────────────────────────────────────────────┐
│  PropertyTest                                                    │
│                                                                  │
│  ┌──────────────┐    ┌──────────────────────────────────────┐   │
│  │ Event        │───>│ E2eTestHarness (Layer 0)              │   │
│  │ Generator    │    │  Real: Coordinator, BGMacroRunner,    │   │
│  │ (randomized) │    │        LeaderKeyListener              │   │
│  └──────────────┘    │  Fake: Keyboard, Screen, Clock, Focus │   │
│                      └───────────────┬──────────────────────┘   │
│                                      │                           │
│                      ┌───────────────▼──────────────────────┐   │
│                      │ Invariant Checker                      │   │
│                      │  After each event, assert:             │   │
│                      │  - No output while game unfocused      │   │
│                      │  - State machine reachable from Idle   │   │
│                      │  - No deadlock (time advances)         │   │
│                      │  - Flask key only when buff inactive   │   │
│                      │  - ...                                 │   │
│                      └────────────────────────────────────────┘  │
│                                                                  │
│  On failure:  seed + event sequence + event log → reproduce      │
└────────────────────────────────────────────────────────────────┘
```

### Event generator

Produces a random sequence from a weighted alphabet of events:

```kotlin
sealed interface TestEvent {
    data class KeyPress(val key: String) : TestEvent
    data class KeyRelease(val key: String) : TestEvent
    data object LeaderKeyChord : TestEvent           // Alt release + X release
    data class SelectMacro(val index: Int) : TestEvent
    data object AltTabAway : TestEvent
    data object AltTabBack : TestEvent
    data class SetFlaskPixel(                        // change what screen returns
        val flaskIndex: Int,
        val active: Boolean,
    ) : TestEvent
    data class AdvanceTime(val ms: Long) : TestEvent  // advance FakeClock
    data object ToggleBgMacros : TestEvent
    data class SwitchConfig(val config: Config) : TestEvent
}
```

Weights ensure realistic distributions (e.g., `AdvanceTime` is frequent, `SwitchConfig` is rare). The generator also respects physical constraints (can't release a key that isn't pressed).

```kotlin
class EventGenerator(private val random: Random) {
    private val pressedKeys = mutableSetOf<String>()

    fun next(): TestEvent {
        val roll = random.nextDouble()
        return when {
            roll < 0.30 -> advanceTime()
            roll < 0.45 -> keyPress()
            roll < 0.60 -> keyRelease()
            roll < 0.70 -> setFlaskPixel()
            roll < 0.78 -> TestEvent.AltTabAway
            roll < 0.86 -> TestEvent.AltTabBack
            roll < 0.92 -> TestEvent.LeaderKeyChord
            roll < 0.96 -> selectMacro()
            roll < 0.98 -> TestEvent.ToggleBgMacros
            else        -> switchConfig()
        }
    }

    private fun advanceTime() = TestEvent.AdvanceTime(
        random.nextLong(10, 2000)  // 10ms to 2s
    )

    // ... other generators respecting physical constraints
}
```

### Invariants

The invariants encode the guardrails (G1–G7) plus general correctness properties:

```kotlin
class InvariantChecker(private val harness: E2eTestHarness) {
    fun checkAfterEvent(event: TestEvent) {
        // G1: No keyboard output while game not in foreground
        if (!harness.activeWindow.isGameFocused) {
            assertThat(harness.keyboardOutput.eventsSince(lastCheck))
                .describedAs("G1: no output while game unfocused")
                .isEmpty()
        }

        // G2: Leader key in Open state → must transition to Idle (not stay Open forever)
        // (checked over a window of events, not per-event)

        // G5: Bg macros independent of fg macro state
        // If bg macros were running before fg macro started, they should still be running
        if (harness.coordinator.state == CoordinatorState.MacroRunning) {
            assertThat(harness.backgroundMacroRunner.isRunning)
                .describedAs("G5: bg macros survive fg macro")
                .isEqualTo(bgMacrosWereRunning)
        }

        // G7: State machine always returns to Idle
        // (checked at end of sequence: advance time by 30s and verify Idle)

        // Liveness: no deadlock
        // The system processes the event within bounded time

        // Safety: flask key pressed only when buff is inactive
        for (press in harness.keyboardOutput.eventsSince(lastCheck)) {
            if (press.keyCode in flaskKeys) {
                assertThat(harness.screen.isBuffActive(press.keyCode))
                    .describedAs("Flask ${press.keyCode} pressed while buff active")
                    .isFalse()
            }
        }
    }
}
```

### Shrinking

When a violation is found with a 500-event sequence, many events are likely irrelevant. A shrinking pass removes events one-by-one and re-runs, finding the minimal sequence that still triggers the violation. This is critical for debugging.

```kotlin
fun shrink(seed: Long, events: List<TestEvent>): List<TestEvent> {
    var minimal = events
    for (i in events.indices.reversed()) {
        val candidate = minimal.toMutableList().apply { removeAt(i) }
        if (stillFails(candidate)) {
            minimal = candidate
        }
    }
    return minimal
}
```

### What it catches that handcrafted tests miss

| Bug class | Example | Why handcrafted misses it |
|-----------|---------|--------------------------|
| Rare race conditions | Leader key arrives during the 1-tick window between focus steal and overlay ready | Hard to reason about timing precisely enough |
| State explosion | Config switch + alt-tab + leader key + bg macro output all within 100ms | Combinatorial — too many permutations to enumerate |
| Deadlocks | Mutex held while waiting on CompletableDeferred that needs the mutex | Only surfaces under specific event orderings |
| Invariant violations at boundaries | Flask key pressed at the exact tick buff transitions from active→inactive | Boundary timing is hard to handcraft |
| Recovery failures | After a rare event sequence, system never returns to Idle | Liveness properties need long random walks to test |

### Practical considerations

- **Speed:** Runs on fake platform, no Win32. Each sequence of 500 events takes ~50ms with `TestScope`. Running 10,000 sequences = ~8 minutes.
- **Determinism:** Seeded `Random`. CI runs with a fixed seed set; local dev runs with random seed and prints it on failure.
- **Flakiness:** Zero — fake platform is fully deterministic.
- **Integration with Layer 0:** Reuses the same `E2eTestHarness`. The only new code is the event generator, invariant checker, and shrinking logic.

---

## Approach B: Reactive game simulator (closed-loop testing)

### Core idea

Replace static pixel recordings with a **game simulator** that reacts to macro output. When the macro presses flask key "3", the simulator shows flask 3's buff as active (changes pixel color). When the buff duration expires, the simulator shows it as inactive. This creates a real feedback loop.

### Why this matters

In production, the system operates in a closed loop:

```
Macro detects buff inactive → presses flask key → game shows buff active → macro detects buff active → stops pressing
```

With static recordings (Layers 1, 4), this loop is broken. The pixel data is predetermined regardless of what the macro does. This means:
- If the macro double-presses a flask, the recording still shows buff activating on schedule — the test can't detect the double-press caused issues
- If the macro never presses (due to a bug), the recording still shows buff expiring on schedule — the test can't distinguish "correct non-press because buff is active" from "bug: macro failed to press"

### Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│  Closed-Loop Test                                                 │
│                                                                   │
│  ┌─────────────┐  key output  ┌────────────────┐                 │
│  │ Macro logic  │────────────>│ Game Simulator  │                 │
│  │ (real)       │             │                  │                 │
│  │              │<────────────│ - Buff model     │                 │
│  │              │  pixel read │ - Flask timers   │                 │
│  └─────────────┘             │ - Focus model    │                 │
│                               └────────────────┘                 │
│                                                                   │
│  Simulator models:                                                │
│  - Flask buff duration (e.g., 5s after key press)                 │
│  - Tincture active indicator                                      │
│  - Alt-tab (pixels go black, game unfocused)                      │
│  - Window focus state                                             │
└─────────────────────────────────────────────────────────────────┘
```

### Game simulator

```kotlin
class GameSimulator(private val clock: FakeClock) : Screen, KeyboardOutputObserver {
    // Buff state model
    private val flaskBuffs = Array(5) { FlaskBuff() }
    private var isFocused = true

    class FlaskBuff(
        var activeUntilMs: Long = 0,  // clock time when buff expires
        val duration: Long = 5000,     // buff lasts 5s
    ) {
        fun activate(now: Long) { activeUntilMs = now + duration }
        fun isActive(now: Long) = now < activeUntilMs
    }

    // React to macro's key output
    override fun onKeyPress(keyCode: String) {
        val flaskIndex = flaskKeyToIndex(keyCode) ?: return
        flaskBuffs[flaskIndex].activate(clock.now)
    }

    // Macro reads pixels from this
    override fun getPixelColor(point: ScreenPoint): ScreenColor {
        if (!isFocused) return ScreenColor(0, 0, 0)  // black when alt-tabbed
        val flaskIndex = pointToFlaskIndex(point) ?: return ScreenColor(0, 0, 0)
        return if (flaskBuffs[flaskIndex].isActive(clock.now)) {
            BUFF_COLOR  // ScreenColor(249, 215, 153)
        } else {
            ScreenColor(30, 25, 20)  // inactive
        }
    }

    fun altTabAway() { isFocused = false }
    fun altTabBack() { isFocused = true }
}
```

### What it catches

| Bug class | Example |
|-----------|---------|
| Double-press spam | Macro presses flask, but detection lag causes it to press again before detecting the buff. Simulator shows buff was already active. |
| Missing press | Macro fails to press expired flask. Simulator keeps buff inactive indefinitely, invariant checker notices. |
| Feedback oscillation | Macro and simulator enter a rapid toggle cycle (press → detect active → stop → detect inactive → press → ...) |
| Recovery after alt-tab | Alt-tab clears buff detection. On tab-back, does the macro correctly re-assess buff state from the simulator's current pixel colors? |
| Timing sensitivity | Buff expires at exactly the wrong moment relative to the macro's polling interval |

### Combining with Approach A

The reactive simulator can be used as the `Screen` implementation inside the property-based testing framework. This gives:
- **Random event sequences** (from Approach A's generator)
- **Closed-loop feedback** (from Approach B's simulator)
- **Invariant checking** (from Approach A's checker)

This combination is the most powerful practical test approach — it randomly explores the state space of a system that operates in a realistic feedback loop.

```kotlin
@RepeatedTest(1000)
fun `system invariants hold under random input with reactive game`(repetition: RepetitionInfo) {
    val seed = repetition.currentRepetition.toLong()
    val random = Random(seed)
    val clock = FakeClock()
    val simulator = GameSimulator(clock)
    val harness = E2eTestHarness(
        screen = simulator,
        keyboardOutputObserver = simulator,  // simulator reacts to key output
        clock = clock,
    )
    val generator = EventGenerator(random)
    val checker = InvariantChecker(harness, simulator)

    val events = (1..500).map { generator.next() }
    for (event in events) {
        harness.apply(event)
        checker.checkAfterEvent(event)
    }
    // Liveness: advance 30s, verify system returns to Idle
    clock.advance(30_000)
    checker.checkLiveness()
}
```

---

## Comparison with Layer 4

| Dimension | Layer 4 (recorded replay) | Approach A (property-based) | Approach B (reactive sim) | A + B combined |
|-----------|--------------------------|---------------------------|--------------------------|----------------|
| State space coverage | ~4 handcrafted scenarios | Thousands of random sequences | Depends on driver | Thousands × closed loop |
| Feedback loop testing | No (static recording) | No (unless combined with B) | Yes | Yes |
| Platform realism | Real Win32, real JNativeHook | Fake platform | Fake platform | Fake platform |
| Speed | ~30s per scenario | ~50ms per sequence | ~50ms per sequence | ~50ms per sequence |
| Flakiness | Medium (real Win32 timing jitter) | Zero (deterministic) | Zero (deterministic) | Zero (deterministic) |
| Setup effort | Record gameplay sessions | Write generator + invariants | Write simulator | Write all three |
| Debugging on failure | Golden output diff | Seed + minimal event sequence | Seed + event sequence + sim state | Full reproduction |
| Bug classes caught | Cross-layer integration | Races, deadlocks, state explosion | Feedback bugs, timing | All of the above |

### What Layer 4 uniquely provides

Layer 4 tests real Win32 integration — JNA bindings, DWM behavior, native hook delivery. Neither A nor B can catch a JNA type mismatch or a `GetPixel` BGR→RGB bug. Layer 2 and Layer 3 cover these individually; Layer 4 covers their interaction.

### Recommended focus

**Start with A+B combined** (property-based testing with reactive game simulator) on the fake platform. This catches the hardest concurrent/integration bugs (the ones that are "really costly to debug" per the task motivation) with zero flakiness and fast iteration.

Layer 4 (real platform replay) is largely superseded by **regression extraction from real gameplay recordings** — see [observability task](../observability.md). Real recordings are strictly better test fixtures than synthetic ones (they capture actual DirectX/DWM/JNativeHook behavior), and they come for free during normal play. Layers 2-3 (individual platform tests) remain valuable for focused API regression testing.

### Simulator validation via observability

The game simulator's fidelity can be validated using session recordings from the [observability task](../observability.md):
- Feed the same macro inputs from a real session recording into the simulator
- Compare the simulator's pixel output against the real pixel reads recorded during gameplay
- Divergences reveal where the simulator model is wrong (e.g., buff duration assumption, color gradient near threshold)
- Fix the simulator, and property-based tests become more meaningful

---

## Implementation sketch for A+B combined

### New classes needed

| Class | Responsibility | LOC estimate |
|-------|---------------|-------------|
| `EventGenerator` | Produces random `TestEvent` sequences respecting physical constraints | ~80 |
| `GameSimulator` | Reactive screen that models flask buffs responding to key output | ~60 |
| `InvariantChecker` | Asserts guardrails and correctness properties after each event | ~80 |
| `PropertyTest` | JUnit test class that wires everything together | ~40 |
| `Shrinker` | Finds minimal failing event sequence | ~40 |

Total: ~300 lines of new test code, reusing the existing `E2eTestHarness` from Layer 0.

### Invariant catalog

| ID | Invariant | Guardrail | Check frequency |
|----|-----------|-----------|-----------------|
| I1 | No keyboard output while game not in foreground | G1 | After every event |
| I2 | Leader key in Open → eventually reaches Idle | G2 | After leader key events |
| I3 | No two fg macros running concurrently | G7 | After every event |
| I4 | Bg macros independent of fg macro lifecycle | G5 | After fg macro state changes |
| I5 | Flask key only pressed when buff is inactive (per simulator) | Correctness | After every output event |
| I6 | No flask key pressed while alt-tabbed | G1 | After every output event |
| I7 | System returns to Idle within 30s of last input | Liveness | End of sequence |
| I8 | No uncaught exceptions or cancelled-but-not-handled coroutines | Correctness | After every event |
