# End to end test

Status: todo
Dependencies: none

## Description

### Motivation

Even though macro-core and macro-overlay have good unit test coverage, real runs of macros (e.g. switch to a game, trigger bg and leader key macros, alt-tab out, and alt-tab back) can still reveal lots of edge cases (e.g. see ./done/bug*).

As we keep add more functionalities or fix existing bugs, we often introduce more integration bugs (e.g. WRT how games or windows work) due to the lack of end to end automated tests.

As we enforce ux-guardrails.md, I imagine e2e tests are also a core part of it.

### Success criteria (draft)

- E2E tests that can run fully automatically, cover my common use cases, and collect useful logs for debugging & replication's purpose in case a test fails.
- E2E tests should also avoid coupling too much with the internals of the implementation: It should only talk to the macro via its interface.

### Ideas

- Randomized property test (covers more cases without manual test case authoring)
- Mock environment: encodes game logic (e.g. flask) and win32 behavior so tests can evaluate by themselves
  + Need a way to verify that the mock is indeed the real behavior.

### Relationship to [observability.md](observability.md)

Testing and observability are complementary:
- Testing verifies behavior under **controlled** conditions (fake platform, property-based, etc.)
- Observability captures behavior under **real** conditions (actual game, actual Win32) — see [observability.md](observability.md)

Interlinks:
- Observability session recordings can feed into **regression extraction** (known-good session → test fixture), largely superseding Layer 4's synthetic recordings
- Session recordings can **validate the game simulator's fidelity** (compare real pixels vs simulator predictions)
- The **invariant catalog** is shared between live monitoring (observability) and property-based tests (this task)

## Plan

See `task/attachment/e2e-test-details.md` for the full design. See `task/attachment/e2e-test-advanced-approaches.md` for property-based testing and reactive game simulator designs.

The plan is organized into **4 layers**, from fast/deterministic to slow/realistic, plus two advanced approaches. Each catches a different class of bug. All run automatically as JUnit 5 tests; layers 2–4 are Windows-only (`@EnabledOnOs(WINDOWS)`).

### Layer 0: Integration harness (fake platform)

Wire together real `Coordinator`, `LeaderKeyListener`, `BackgroundMacroRunner`, `MacroRunnerImpl` with fake platform I/O. No native code, runs on any OS.

**What it catches:** State machine bugs, concurrency races, output suppression, guardrail violations (G1–G7). These are the bugs from `done/bugs-overlay-focus.md` (Bug 2, 4, 5).

**Harness:**

```kotlin
class E2eTestHarness(testScope: TestScope) {
    // Platform fakes (test controls)
    val keyboard: FakeKeyboardInput
    val keyboardOutput: FakeKeyboardOutput
    val screen: FakeScreen
    val activeWindow: FakeActiveWindowChecker
    val clock: FakeClock

    // Real components (system under test)
    val coordinator: Coordinator
    val backgroundMacroRunner: BackgroundMacroRunner
    val leaderKeyListener: LeaderKeyListener

    // High-level actions
    suspend fun pressLeaderKey()
    suspend fun selectMacro(index: Int)
    suspend fun altTabAway()
    suspend fun altTabBack()
}
```

**Scenarios (8 tests):**

| # | Scenario | Guardrails |
|---|----------|------------|
| 1 | Leader key → select → macro runs → idle | G6, G7 |
| 2 | Leader key toggle (second press dismisses) | G2 |
| 3 | Leader key during macro running = no-op | G2, G7 |
| 4 | Alt-tab while picker open → auto-cancel | G1 |
| 5 | Alt-tab while macro running → macro continues | G1, G5 |
| 6 | Bg macros + overlay independence + output suppression | G4, G5 |
| 7 | Bg macros continue on alt-tab | G1, G5 |
| 8 | Reopen after cancel (no stuck state) | G7 |

**Module placement:** `macro-app/src/test/`

### Layer 1: Game behavior replay (fake platform, real pixel data)

Test flask/tincture detection and timing against **captured pixel data from real gameplay**. Still uses fake platform (no Win32 calls), but feeds realistic screen colors through `FakeScreen`.

**What it catches:** Color threshold bugs (`distanceTo < 10` too tight/loose), buff timing bugs (gap fixer fires too early/late, throttle too aggressive), config switching bugs (old keepers survive). These are the hardest to debug in production because you need the game running to reproduce.

**Approach: Record → Fixture → Replay**

1. **Record** (manual, one-time): Run a small capture utility during real gameplay that samples pixel colors at flask bar positions (`PoeFlasks.X_COORDS[i]`, `Y_COORD`) and tincture positions every 50ms. Save as a CSV timeline:
   ```
   timestamp_ms, flask0_r, flask0_g, flask0_b, flask1_r, ..., tincture_r, tincture_g, tincture_b
   0,    249, 215, 153,  0, 0, 0,  ...   # flask 0 active, flask 1 inactive
   50,   249, 215, 153,  0, 0, 0,  ...
   100,  245, 210, 148,  0, 0, 0,  ...   # flask 0 fading
   150,  30,  25,  20,   0, 0, 0,  ...   # flask 0 expired
   ```

2. **Fixture**: Store CSVs as test resources. One per game scenario:
   - `flask-expires-naturally.csv` — flask buff runs out, should re-press
   - `flask-active-steady.csv` — buff stays active, should NOT re-press
   - `tincture-active.csv` — red light active indicator
   - `alt-tab-and-back.csv` — pixel reads return black (0,0,0) while alt-tabbed (game not rendering), then real colors on tab-back

3. **Replay**: `TimelineScreen` fake plays back the CSV, advancing pixel colors as `FakeClock` advances:
   ```kotlin
   class TimelineScreen(private val timeline: List<PixelSnapshot>) : Screen {
       var currentTimeMs: Long = 0
       override fun getPixelColor(point: ScreenPoint): ScreenColor {
           val snapshot = timeline.lastOrNull { it.timestampMs <= currentTimeMs }
           return snapshot?.colorAt(point) ?: ScreenColor(0, 0, 0)
       }
   }
   ```

**Test scenarios:**

| # | Scenario | What it validates |
|---|----------|-------------------|
| 1 | Flask expires → re-pressed within 2s (gap fixer) | `isDurationBarActive` threshold, gap fixer timing |
| 2 | Flask active → NOT re-pressed (no spam) | `SkipIfTooFrequent` throttle, `isBuffInEffect` correctness |
| 3 | Tincture active (red light OR duration bar) | Dual-check logic in `tinctureKeeper` |
| 4 | Alt-tab → black pixels → tab back → correct detection | No false positive on black pixels, recovery on tab-back |
| 5 | Config switch mid-session → old keepers cancelled | `collectLatest` cancellation, no stale key presses |
| 6 | `AlternatingBuffKeeper` round-robin with real color data | Alternation throttle (500ms), `isBuffInEffect` any-vs-all |
| 7 | `ParallelBuffKeeper` staggered trigger timing | Stagger variance, concurrent trigger correctness |

**Capture utility** (new, small): A main function that initializes `Win32Screen`, reads flask pixel positions in a loop, and writes the CSV. ~30 lines. Run it manually before a game session to generate fixtures.

### Layer 2: Platform integration tests (real Win32 APIs, test windows)

Exercise the real `Win32FocusManager`, `Win32ActiveWindowChecker`, `Win32Screen` against **test windows we create** (not the game). `@EnabledOnOs(WINDOWS)`.

**What it catches:** Win32 API regressions, JNA binding errors, HiDPI scaling bugs, focus stealing failures. These are Bug 3's category — things that work in code review but break on real Windows.

**Approach:** Create lightweight Swing/AWT test windows with known properties, then exercise Win32 implementations against them.

**Tests:**

| # | Test | Implementation |
|---|------|----------------|
| 1 | `Win32ActiveWindowChecker` detects foreground window | Create a Swing frame with title "TestGame", call `toFront()`, assert `isActiveWindow(setOf("TestGame"))` returns true |
| 2 | `Win32ActiveWindowChecker` exact title match | Assert `isActiveWindow(setOf("TestGam"))` returns false (substring doesn't match) |
| 3 | `Win32FocusManager.captureActivationContext()` | Bring test window to front, verify returned title matches |
| 4 | `Win32FocusManager.stealFocusToOverlay()` | Create two windows, focus window A, call `stealFocusToOverlay("B")`, verify B is now foreground |
| 5 | `Win32FocusManager.returnFocusToGame()` | Steal focus away, then return it, verify original window is foreground again |
| 6 | `Win32Screen.getPixelColor()` reads from test window | Create a Swing frame filled with `Color(249, 215, 153)`, verify `getPixelColor` at that position returns the same RGB |
| 7 | `Win32Screen.getPixelColor()` BGR→RGB conversion | Paint a window with `Color(255, 0, 0)` (pure red), verify we get `ScreenColor(255, 0, 0)` (not blue — GDI32 returns BGR COLORREF) |
| 8 | `Win32Screen.captureScreen()` HiDPI scaling | Verify captured image dimensions match physical resolution, pixel at known position is correct |
| 9 | `setClickThrough()` adds WS_EX_TRANSPARENT | Call it, then read back the window style via `GetWindowLongA`, verify the bit is set |
| 10 | `excludeWindowFromCapture()` | Call it, then do a Robot capture — test window should NOT appear in the capture (reads as black/desktop) |

**Lifecycle:** Each test creates a `JFrame`, runs the test, and disposes the frame in an `@AfterEach`. Tests are `@Isolated` (JUnit parallel disabled) since they manipulate global window focus.

### Layer 3: JNativeHook loopback tests (real native hooks)

Test that JNativeHook's event posting and listening work correctly end-to-end on Windows. `@EnabledOnOs(WINDOWS)`.

**What it catches:** Key code mapping errors (string name → `VC_*` constant), event delivery failures, flow backpressure issues, `callbackFlow` lifecycle bugs.

**Approach:** Initialize `GlobalScreen`, register hook listeners, post synthetic events, verify they're received.

**Tests:**

| # | Test | What it validates |
|---|------|-------------------|
| 1 | Post key press → hook receives it | Basic loopback: `JNativeHookKeyboardOutput.postPress("W")` → `JNativeHookKeyboardInput.keyPresses()` emits `"W"` |
| 2 | Post key release → hook receives it | Same for release path |
| 3 | Multiple collectors receive same event | Two `.keyPresses()` flows both see the event (non-exclusive delivery — G4) |
| 4 | Key name round-trip for all mapped keys | For each key in the mapping table (Ctrl, Alt, Shift, Enter, /, A–Z, 1–9): post → receive → verify same name |
| 5 | Mouse move → hook receives coordinates | `JNativeHookMouseOutput.moveTo(point)` → `JNativeHookMouseInput.motionEvents()` emits matching point |
| 6 | Rapid key sequence ordering | Post A, B, C in quick succession, verify flow emits them in order |

**Lifecycle:** `GlobalScreen.registerNativeHook()` in `@BeforeAll`, `unregisterNativeHook()` in `@AfterAll`. These tests are **slow** (~100ms per event for native hook latency) and isolated.

### Layer 4: Full scenario replay (real platform, recorded sessions)

Replay a **recorded interaction session** through the full stack (real Win32 APIs + real macro logic), but against test windows instead of the actual game. `@EnabledOnOs(WINDOWS)`.

**What it catches:** Integration bugs between layers — e.g., focus stealing races (Bug 3), pixel reading while overlay is visible, JNativeHook event delivery while focus changes.

**Approach: Record → Replay with test windows**

1. **Recording format**: Extends Layer 1's pixel timeline with key events and focus changes:
   ```
   type, timestamp_ms, data
   KEY_PRESS, 0, W
   PIXEL, 50, flask0=249:215:153, flask1=0:0:0
   KEY_RELEASE, 500, W
   FOCUS, 600, Desktop          # alt-tab away
   FOCUS, 2000, Path of Exile   # alt-tab back
   KEY_PRESS, 2100, W
   ```

2. **Replay driver**: A test harness that:
   - Creates two Swing windows: "Path of Exile" (painted with recorded pixel colors) and "Desktop"
   - Uses real `Win32FocusManager` to switch between them at recorded timestamps
   - Uses real `JNativeHookKeyboardOutput` to inject key events at recorded timestamps
   - Runs real `BackgroundMacroRunner` + `Coordinator` against real `Win32Screen` + `Win32ActiveWindowChecker`
   - Asserts on the output: which keys were pressed, when, and in what order

3. **Reference output**: The first run of a recorded session produces a "golden" output log. Subsequent runs compare against it (snapshot testing). Differences indicate a regression.

**Scenarios** (recorded during real gameplay or against test windows):

| # | Scenario | Bug class |
|---|----------|-----------|
| 1 | Bg macros running → Alt+X → pick macro → macro runs → idle | Bug 3 (focus race), Bug 5 (toggle) |
| 2 | Flask macro active → alt-tab → tab back → flasks resume | Alt-tab pixel recovery |
| 3 | Rapid Alt+X double-tap (open → immediate cancel) | Timing race between leader key and overlay |
| 4 | Bg macro output during overlay focus steal | Output suppression timing |

### Approach A: Property-based testing (randomized invariant checking)

Generate random sequences of input events (key presses, focus changes, pixel changes, config switches) on the **fake platform** (Layer 0 harness) and assert system invariants hold after every event. Catches races, deadlocks, and state explosion bugs that handcrafted scenarios miss. Deterministic via seeded `Random`, zero flakiness. See `task/attachment/e2e-test-advanced-approaches.md` for event generator, invariant catalog, and shrinking design.

**What it catches:** Rare race conditions, state explosion from event combinations no one thought to test, deadlocks, liveness violations (system never returns to Idle).

**Invariant catalog** (shared with [observability.md](observability.md) live monitoring):

| ID | Invariant | Guardrail |
|----|-----------|-----------|
| I1 | No keyboard output while game not in foreground | G1 |
| I2 | Leader key in Open → eventually reaches Idle | G2 |
| I3 | No two fg macros running concurrently | G7 |
| I4 | Bg macros independent of fg macro lifecycle | G5 |
| I5 | Flask key only pressed when buff is inactive (per simulator) | Correctness |
| I6 | No flask key pressed while alt-tabbed | G1 |
| I7 | System returns to Idle within 30s of last input | Liveness |
| I8 | No uncaught exceptions or unhandled coroutine cancellation | Correctness |

### Approach B: Reactive game simulator (closed-loop testing)

Replace static pixel recordings with a `GameSimulator` that reacts to macro key output: pressing flask key → buff becomes active → pixel color changes → macro detects buff → stops pressing. Creates a closed feedback loop. See `task/attachment/e2e-test-advanced-approaches.md` for `GameSimulator` design.

**What it catches:** Feedback loop bugs (double-press spam, oscillation), timing sensitivity (buff expires at exactly the macro's polling boundary), recovery after alt-tab in a dynamic environment.

**Combines with Approach A:** Use `GameSimulator` as the `Screen` inside the property-based test. Random inputs + closed-loop feedback + invariant checking = the most powerful practical test approach.

**Simulator validation:** Compare simulator pixel output against real gameplay recordings from [observability.md](observability.md) session logs. Divergences reveal where the simulator model is wrong.

### Logging & diagnostics (all layers)

When any test fails, produce a log that enables reproduction:

- **Event log:** Timestamped sequence of all inputs/outputs and state transitions
- **Assertion context:** On failure, dump the event log + current state snapshot

```kotlin
data class LogEntry(
    val timestampMs: Long,
    val source: String,       // "keyboard.in", "coordinator", "overlay", "bgMacro", "win32.focus"
    val message: String,
)
```

Implementation: Logging decorators wrapping each component. JUnit `@ExtendWith(EventLogExtension::class)` dumps on failure.

### Cross-macro feedback (G4a)

Test the intentional auto-attack → flask feedback loop. Requires a `LoopbackKeyboardOutput` that writes to both the recording output and the keyboard input (simulating how JNativeHook hooks see injected keys in production).

For Layer 0 (fake platform): `LoopbackKeyboardOutput` bridges `FakeKeyboardOutput` → `FakeKeyboardInput`.
For Layer 3+: JNativeHook naturally loops back (posted events are seen by hooks).

### Build setup

- Layer 0: `macro-app/src/test/` — needs `testImplementation` access to `macro-core` test fixtures (use Gradle `java-test-fixtures` plugin)
- Layers 1–4: `macro-app/src/test/` with `@EnabledOnOs(WINDOWS)` annotations
- Capture utility: `macro-app/src/main/` or a small standalone `main` in test sources (only used manually)
- Pixel fixtures: `macro-app/src/test/resources/fixtures/` (CSV files)

### Open questions

1. **Test window pixel stability**: When we create a Swing `JFrame` painted with known colors for Layer 2, will `Win32Screen.getPixelColor()` reliably read those colors? Potential issues: DWM composition, window decorations, rendering pipeline delays. **Mitigation:** Use undecorated frames, add a small delay after `setVisible(true)`, verify pixel before asserting.

2. **JNativeHook in test process**: Layer 3 requires `GlobalScreen.registerNativeHook()` in the test JVM. This installs global keyboard/mouse hooks on the OS. Risk: interferes with developer's active use of the machine during test run. **Mitigation:** Run these tests only in CI or with a dedicated `./gradlew testWin32` task, not in default `./gradlew test`.

3. **Layer 4 test window as game substitute**: We paint test windows to mimic game pixels, but real games render via DirectX/Vulkan (not GDI). `GetPixel` on a GDI DC might not see DirectX-rendered content. However, our test windows use Swing (which paints via GDI), so `GetPixel` should work for them. The gap is: we're testing "can we read GDI windows correctly" not "can we read the actual game." Overlay's `excludeFromCapture` uses `WDA_EXCLUDEFROMCAPTURE` which works at the DWM level and should be game-independent.

4. **Recording effort**: Layer 1 fixtures need to be captured from real gameplay. How much effort is the initial recording? **Estimate:** Write the capture utility (~30 lines), play for 2–3 minutes per scenario, save CSVs. Total: ~1 hour for initial fixture set. Re-recording needed only if flask UI changes (game patch).

## Acceptance Criteria

- [ ] **Layer 0:** `E2eTestHarness` wires real Coordinator + LeaderKeyListener + BackgroundMacroRunner with fake platform I/O
- [ ] **Layer 0:** Scenarios 1–8 pass as automated JUnit 5 tests
- [ ] **Layer 1:** Capture utility records flask pixel timelines from real gameplay
- [ ] **Layer 1:** `TimelineScreen` replays pixel data; flask timing scenarios pass
- [ ] **Layer 2:** Win32 platform tests pass against test windows (`@EnabledOnOs(WINDOWS)`)
- [ ] **Layer 3:** JNativeHook loopback tests validate event round-trip
- [ ] **Layer 4:** At least one full scenario replay test with golden output comparison
- [ ] **Approach A:** Property-based test runs 1000+ random sequences against Layer 0 harness, checking invariant catalog
- [ ] **Approach A:** Shrinking produces minimal reproducing sequence on invariant violation
- [ ] **Approach B:** `GameSimulator` models flask buff lifecycle (activate on key press, expire after duration)
- [ ] **Approach A+B:** Property-based test with reactive simulator as `Screen` implementation
- [ ] **Shared:** Invariant catalog is defined once and used by both property tests and [observability](observability.md) live monitoring
- [ ] Event logging produces useful diagnostics on failure
- [ ] Each test documents which layer and guardrail(s) it covers
- [ ] Layers 2–4 are isolated from default `./gradlew test` (separate task or `@Tag`)
