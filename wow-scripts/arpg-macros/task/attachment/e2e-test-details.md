# E2E Test — Detailed Design

## Layer architecture

4 layers, from fast/deterministic to slow/realistic. Each catches a different class of bug.

```
Layer 0: Integration harness       │ Fake platform, any OS     │ ~1s    │ State machine, races, guardrails
Layer 1: Game behavior replay      │ Fake platform, real pixels│ ~2s    │ Color thresholds, buff timing
Layer 2: Platform integration      │ Real Win32, test windows  │ ~5s    │ Focus stealing, pixel reading
Layer 3: JNativeHook loopback      │ Real native hooks         │ ~10s   │ Event delivery, key mapping
Layer 4: Full scenario replay      │ Real everything, no game  │ ~30s   │ Cross-layer integration
```

---

## Layer 0: Integration harness (fake platform)

### Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│  E2eTestHarness                                                 │
│                                                                 │
│  ┌──────────────┐    ┌────────────────┐    ┌────────────────┐   │
│  │ FakeKeyboard │───>│ LeaderKeyListener│──>│  Coordinator   │   │
│  │   Input      │    └────────────────┘    │  (real)        │   │
│  └──────────────┘                          └───────┬────────┘   │
│                                                    │            │
│  ┌──────────────┐    ┌────────────────┐    ┌───────┴────────┐   │
│  │ FakeActive   │───>│ BackgroundMacro│    │ FakeOverlay    │   │
│  │ WindowChecker│    │ Runner (real)  │    │ Controller     │   │
│  └──────────────┘    └────────────────┘    └────────────────┘   │
│                                                                 │
│  ┌──────────────┐    ┌────────────────┐                         │
│  │ FakeKeyboard │<── │ Reporting      │                         │
│  │   Output     │    │ KeyboardOutput │                         │
│  └──────────────┘    └────────────────┘                         │
│                                                                 │
│  ┌──────────────┐    ┌──────────────┐                           │
│  │ FakeScreen   │    │ EventLog     │◄── all components log     │
│  └──────────────┘    └──────────────┘                           │
└─────────────────────────────────────────────────────────────────┘
```

### Fake components

**FakeOverlayController** — enhanced version of CoordinatorTest's fake:

```kotlin
class E2eFakeOverlayController : OverlayController {
    var awaitSelectionCalls = 0
    var cancelSelectionCalls = 0
    var showStatusCalls = mutableListOf<String>()
    var hideStatusCalls = 0
    var currentMacros: List<MacroRegistration> = emptyList()
    var bgState: BackgroundMacroState? = null

    private var selectionDeferred = CompletableDeferred<OverlaySelection>()

    override suspend fun awaitSelection(macros, context): OverlaySelection {
        awaitSelectionCalls++
        currentMacros = macros
        return selectionDeferred.await()
    }

    override fun cancelSelection() {
        cancelSelectionCalls++
        selectionDeferred.complete(OverlaySelection.Cancelled)
    }

    override fun showExecutionStatus(macroName: String) { showStatusCalls += macroName }
    override fun hideExecutionStatus() { hideStatusCalls++ }
    override fun connectBackgroundMacros(state: BackgroundMacroState) { bgState = state }

    // Test API
    fun selectMacro(index: Int) {
        selectionDeferred.complete(OverlaySelection.Selected(currentMacros[index]))
    }
    fun resetDeferred() { selectionDeferred = CompletableDeferred() }
}
```

**FakeFocusManager** — records calls, configurable foreground:

```kotlin
class E2eFakeFocusManager : FocusManager {
    var foregroundGame: String? = "Path of Exile"
    var stealFocusCalls = 0
    var returnFocusCalls = 0

    override fun captureActivationContext(): ActivationContext? {
        val title = foregroundGame ?: return null
        return ActivationContext(null, title, ScreenPoint(100, 100))
    }
    override fun stealFocusToOverlay(title: String) { stealFocusCalls++ }
    override fun returnFocusToGame(ctx: ActivationContext) { returnFocusCalls++ }
    override fun excludeWindowFromCapture(title: String) {}
    override fun setClickThrough(title: String, enabled: Boolean) {}
}
```

### Scenario details

**Scenario 1: Happy path** (G6, G7)
```
given: game in foreground, bg macros disabled
when:  emit Alt release, X release (leader chord)
then:  coordinator.state = Open, overlay.awaitSelectionCalls = 1
when:  overlay.selectMacro(0)
then:  coordinator.state = MacroRunning, overlay.showStatusCalls = ["Test Macro"]
when:  macro completes
then:  coordinator.state = Idle, overlay.hideStatusCalls = 1
```

**Scenario 4: Alt-tab while picker open** (G1) — the subtlety:

In production, the Compose `LaunchedEffect` monitors `activeWindowFlow()` and calls `cancelSelection()`. In the harness, we replicate this with a harness-level coroutine:

```kotlin
// In harness setup
launch {
    activeWindowChecker.activeWindowFlow(gameTitles + overlayTitle).collect { isFocused ->
        if (!isFocused && coordinator.state == CoordinatorState.Open) {
            overlayController.cancelSelection()
        }
    }
}
```

This tests the full flow: alt-tab → active window changes → polling detects it → cancel fires → state = Idle. The polling interval (`advanceTimeBy(100)`) is a documented test convention.

**Scenario 6: Bg macros + overlay independence** (G4, G5) — the key assertion:

```
given: bg macros enabled, game in foreground, W held (flask macro active)
       keyboardOutput records flask key presses (e.g., "3")
when:  press leader key → state = Open
then:  backgroundMacroRunner.outputSuppressed = true
       keyboardOutput stops receiving new flask presses
when:  overlay.selectMacro(0) → fg macro runs → completes
then:  backgroundMacroRunner.outputSuppressed = false
       keyboardOutput resumes receiving flask presses
```

### Build dependencies

`macro-app/build.gradle.kts` needs `testImplementation` on `macro-core`'s test fixtures. Use Gradle `java-test-fixtures` plugin to expose `FakePlatform.kt` classes without duplication.

---

## Layer 1: Game behavior replay (fake platform, real pixel data)

### The hard problem

Flask detection relies on:
- Euclidean distance from `BUFF_COLOR(249, 215, 153)` with threshold `< 10`
- Tincture active color `(164, 83, 40)` with threshold `< 15`
- Pixel positions hardcoded for 2560x1440

Bugs here are expensive: you need the game running, the right flask active, at the right screen position. If the color threshold is wrong by 1 unit, flasks spam or never re-press.

### Approach: Record → Fixture → Replay

**Step 1: Capture utility** (~30 lines, run manually during gameplay)

```kotlin
fun main() {
    val screen = Win32Screen()
    val positions = PoeFlasks.X_COORDS.mapIndexed { ix, x ->
        "flask$ix" to ScreenPoint(x, PoeFlasks.Y_COORD)
    } + listOf(
        "tincture" to ScreenPoint(PoeFlasks.TINCTURE_X, PoeFlasks.TINCTURE_Y)
    )
    val writer = File("flask-capture.csv").bufferedWriter()
    writer.write("timestamp_ms," + positions.joinToString(",") { "${it.first}_r,${it.first}_g,${it.first}_b" })
    writer.newLine()

    val start = System.currentTimeMillis()
    while (true) {
        val t = System.currentTimeMillis() - start
        val colors = positions.map { screen.getPixelColor(it.second) }
        writer.write("$t," + colors.joinToString(",") { "${it.red},${it.green},${it.blue}" })
        writer.newLine()
        Thread.sleep(50)
    }
}
```

Run during gameplay for 2–3 minutes per scenario. This captures the pixel timeline.

**Step 2: Fixtures** (stored in `macro-app/src/test/resources/fixtures/`)

| Fixture | Game scenario | Duration |
|---------|--------------|----------|
| `flask-expires-naturally.csv` | Pop a flask, wait for it to expire, see it re-pressed | ~10s |
| `flask-active-steady.csv` | Hold W with active flasks, no re-pressing needed | ~5s |
| `tincture-active.csv` | Tincture with red active indicator | ~5s |
| `alt-tab-black-pixels.csv` | Alt-tab away (pixels go black), tab back | ~5s |
| `flask-multiple-configs.csv` | Different flask configs (1Q, 2Q, all) | ~15s |
| `near-threshold-colors.csv` | Flasks at various durations (color gradient near threshold) | ~10s |

**Step 3: TimelineScreen** (plays back fixtures)

```kotlin
class TimelineScreen(
    private val timeline: List<PixelSnapshot>,
    private val clock: FakeClock,
) : Screen {
    override fun getPixelColor(point: ScreenPoint): ScreenColor {
        val snapshot = timeline.lastOrNull { it.timestampMs <= clock.now }
        return snapshot?.colorAt(point) ?: ScreenColor(0, 0, 0)
    }

    override fun captureScreen(): PixelSource = object : PixelSource {
        override fun getPixelColor(point: ScreenPoint) = this@TimelineScreen.getPixelColor(point)
    }
}

data class PixelSnapshot(
    val timestampMs: Long,
    val colors: Map<ScreenPoint, ScreenColor>,
) {
    fun colorAt(point: ScreenPoint) = colors[point] ?: ScreenColor(0, 0, 0)
}
```

### Test scenarios

**1. Flask expires → re-pressed within 2s**
```
given: TimelineScreen loaded with flask-expires-naturally.csv
       AutoFlaskMacro running with Config.One(1)
       W held (via FakeKeyboardInput)
when:  advance clock through timeline (buff active → buff expires)
then:  keyboardOutput shows "1" pressed shortly after buff expires
       gap between expiry and re-press < 2s (gap fixer window)
```

**2. Flask active → NOT re-pressed**
```
given: flask-active-steady.csv, W held
when:  advance through 5 seconds of active buff
then:  no flask key pressed (isBuffInEffect() returns true, throttle prevents re-press)
```

**3. Tincture dual-check (red light OR duration bar)**
```
given: tincture-active.csv
when:  tincture active indicator shows → duration bar fades
then:  isBuffInEffect() returns true while EITHER check passes
       re-press only after BOTH indicators go inactive
```

**4. Alt-tab black pixels**
```
given: alt-tab-black-pixels.csv (pixels = 0,0,0 while alt-tabbed)
       game not in foreground (FakeActiveWindowChecker.active = false)
when:  advance through alt-tab period
then:  black pixels (0,0,0) are far from BUFF_COLOR → isBuffInEffect = false
       BUT: active() returns false (isPoe = false) → no flask pressing
       → no false positive spam while alt-tabbed
when:  tab back (activeWindow = game, pixels return to real colors)
then:  flask detection resumes correctly
```

**5. Config switch cancels old keepers**
```
given: AutoFlaskMacro running with Config.One(3)
       W pressed → key "3" being sent
when:  selectConfig(PoeFlasks.leveling2Qs) → Config.alt(4, 5)
       advance past throttle (1100ms)
       W pressed
then:  keyboardOutput contains "4" or "5"
       keyboardOutput does NOT contain "3" (old keeper cancelled)
```

**6. AlternatingBuffKeeper round-robin**
```
given: Config.alt(4, 5) → AlternatingBuffKeeper
       flask-expires-naturally.csv for both flask 4 and 5
when:  both expire, trigger called repeatedly
then:  keys alternate: "4", "5", "4", "5" (with 500ms throttle between)
```

**7. ParallelBuffKeeper staggered timing**
```
given: Config.par(1, 2, 3) → ParallelBuffKeeper
       all three flasks expired
when:  trigger() called
then:  keys "1", "2", "3" all pressed
       timing is staggered (0–20ms random delay between each)
```

### Threshold boundary testing

Additionally, test `isDurationBarActive` and `tinctureKeeper.isBuffInEffect` with synthetic pixel data at the boundary:

```kotlin
@ParameterizedTest
@CsvSource(
    "249,215,153, true",   // exact BUFF_COLOR
    "250,216,154, true",   // distance ~1.7 (within 10)
    "255,220,160, true",   // distance ~9.3 (within 10)
    "256,221,161, false",  // distance ~10.4 (outside 10)
    "0,0,0, false",        // black (alt-tabbed)
    "240,205,143, true",   // slightly darker (within 10)
    "230,195,133, false",  // too far (distance ~27)
)
fun `flask detection threshold`(r: Int, g: Int, b: Int, expected: Boolean)
```

---

## Layer 2: Platform integration tests (real Win32, test windows)

### Setup pattern

Each test creates an undecorated `JFrame`, runs the Win32 API call, and asserts:

```kotlin
@EnabledOnOs(OS.WINDOWS)
@Tag("win32")
class Win32FocusManagerTest {
    private lateinit var frame: JFrame

    @BeforeEach
    fun setup() {
        frame = JFrame("TestGame").apply {
            isUndecorated = true
            setSize(200, 200)
            setLocationRelativeTo(null)
            isVisible = true
            toFront()
        }
        // Give DWM time to render
        Thread.sleep(200)
    }

    @AfterEach
    fun teardown() {
        frame.dispose()
    }
}
```

### Tests

**Win32ActiveWindowChecker:**

```kotlin
@Test
fun `detects foreground window by exact title`() {
    val checker = Win32ActiveWindowChecker()
    frame.toFront()
    Thread.sleep(100)
    assertThat(checker.isActiveWindow(setOf("TestGame"))).isTrue()
}

@Test
fun `rejects substring mismatch`() {
    val checker = Win32ActiveWindowChecker()
    frame.toFront()
    Thread.sleep(100)
    assertThat(checker.isActiveWindow(setOf("TestGam"))).isFalse()
    assertThat(checker.isActiveWindow(setOf("TestGame "))).isFalse()
}
```

**Win32FocusManager:**

```kotlin
@Test
fun `stealFocusToOverlay changes foreground window`() {
    val overlay = JFrame("TestOverlay").apply { isUndecorated = true; setSize(100,100); isVisible = true }
    try {
        frame.toFront(); Thread.sleep(100)
        val fm = Win32FocusManager()
        fm.stealFocusToOverlay("TestOverlay")
        Thread.sleep(100)
        // Verify overlay is now foreground
        val checker = Win32ActiveWindowChecker()
        assertThat(checker.isActiveWindow(setOf("TestOverlay"))).isTrue()
    } finally { overlay.dispose() }
}

@Test
fun `returnFocusToGame restores original window`() {
    val fm = Win32FocusManager()
    frame.toFront(); Thread.sleep(100)
    val ctx = fm.captureActivationContext()!!
    assertThat(ctx.gameTitle).isEqualTo("TestGame")

    // Steal focus away
    val other = JFrame("Other").apply { isUndecorated = true; setSize(100,100); isVisible = true; toFront() }
    try {
        Thread.sleep(100)
        fm.returnFocusToGame(ctx)
        Thread.sleep(100)
        val checker = Win32ActiveWindowChecker()
        assertThat(checker.isActiveWindow(setOf("TestGame"))).isTrue()
    } finally { other.dispose() }
}
```

**Win32Screen:**

```kotlin
@Test
fun `getPixelColor reads correct RGB from painted window`() {
    // Paint a known color
    val targetColor = java.awt.Color(249, 215, 153)  // BUFF_COLOR
    frame.contentPane.background = targetColor
    frame.contentPane.repaint()
    Thread.sleep(200)

    val screen = Win32Screen()
    val loc = frame.locationOnScreen
    val center = ScreenPoint(loc.x + 100, loc.y + 100)
    val color = screen.getPixelColor(center)

    // Allow ±1 for rounding
    assertThat(color.red).isCloseTo(249, within(1))
    assertThat(color.green).isCloseTo(215, within(1))
    assertThat(color.blue).isCloseTo(153, within(1))
}

@Test
fun `getPixelColor BGR conversion is correct for pure red`() {
    frame.contentPane.background = java.awt.Color(255, 0, 0)
    frame.contentPane.repaint(); Thread.sleep(200)
    val screen = Win32Screen()
    val loc = frame.locationOnScreen
    val color = screen.getPixelColor(ScreenPoint(loc.x + 100, loc.y + 100))
    assertThat(color.red).isEqualTo(255)
    assertThat(color.green).isEqualTo(0)
    assertThat(color.blue).isEqualTo(0)
}
```

**Window style manipulation:**

```kotlin
@Test
fun `setClickThrough adds WS_EX_TRANSPARENT style`() {
    val fm = Win32FocusManager()
    fm.setClickThrough("TestGame", enabled = true)
    // Read back style
    val hwnd = User32.INSTANCE.FindWindow(null, "TestGame")
    val style = User32Ext.INSTANCE.GetWindowLongA(hwnd, GWL_EXSTYLE)
    assertThat(style and WS_EX_TRANSPARENT).isNotZero()
}

@Test
fun `excludeWindowFromCapture makes Robot capture miss the window`() {
    frame.contentPane.background = java.awt.Color.RED
    frame.contentPane.repaint(); Thread.sleep(200)

    val fm = Win32FocusManager()
    fm.excludeWindowFromCapture("TestGame")

    val robot = Robot()
    val loc = frame.locationOnScreen
    val capture = robot.createScreenCapture(Rectangle(loc.x + 50, loc.y + 50, 1, 1))
    val pixel = capture.getRGB(0, 0)
    // Should NOT be red — the window is excluded from capture
    val r = (pixel shr 16) and 0xFF
    assertThat(r).isNotEqualTo(255)
}
```

### Reliability notes

- Tests use `Thread.sleep(200)` after window operations to let DWM render. This is inherently slightly flaky but unavoidable for real Win32 tests.
- Use `@RepeatedTest(3)` for the most timing-sensitive tests and assert at least 2/3 pass.
- Tests should not run in parallel with each other (they compete for foreground focus). Use `@Isolated` or a single-threaded executor.

---

## Layer 3: JNativeHook loopback tests

### Setup

```kotlin
@EnabledOnOs(OS.WINDOWS)
@Tag("jnativehook")
class JNativeHookLoopbackTest {
    companion object {
        @BeforeAll @JvmStatic
        fun init() { GlobalScreen.registerNativeHook() }
        @AfterAll @JvmStatic
        fun cleanup() { GlobalScreen.unregisterNativeHook() }
    }
}
```

### Tests

**Basic loopback:**
```kotlin
@Test
fun `posted key press is received by listener`() = runBlocking {
    val input = JNativeHookKeyboardInput()
    val output = JNativeHookKeyboardOutput()
    val received = CompletableDeferred<String>()

    val job = launch {
        input.keyPresses().first().let { received.complete(it) }
    }
    delay(100) // let listener register

    output.postPress("A")
    val key = withTimeout(2000) { received.await() }
    assertThat(key).isEqualTo("A")
    job.cancel()
}
```

**Multiple collectors (G4):**
```kotlin
@Test
fun `two collectors both receive the same key event`() = runBlocking {
    val input = JNativeHookKeyboardInput()
    val output = JNativeHookKeyboardOutput()
    val received1 = CompletableDeferred<String>()
    val received2 = CompletableDeferred<String>()

    val job1 = launch { input.keyPresses().first().let { received1.complete(it) } }
    val job2 = launch { input.keyPresses().first().let { received2.complete(it) } }
    delay(100)

    output.postPress("B")
    assertThat(withTimeout(2000) { received1.await() }).isEqualTo("B")
    assertThat(withTimeout(2000) { received2.await() }).isEqualTo("B")
    job1.cancel(); job2.cancel()
}
```

**Key name round-trip:**
```kotlin
@ParameterizedTest
@ValueSource(strings = ["A", "B", "W", "1", "3", "5", "Ctrl", "Alt", "Shift", "Enter", "/"])
fun `key name survives output-input round-trip`(keyName: String) = runBlocking {
    val input = JNativeHookKeyboardInput()
    val output = JNativeHookKeyboardOutput()
    val received = CompletableDeferred<String>()
    val job = launch { input.keyPresses().first().let { received.complete(it) } }
    delay(100)
    output.postPress(keyName)
    assertThat(withTimeout(2000) { received.await() }).isEqualTo(keyName)
    job.cancel()
}
```

**Ordering:**
```kotlin
@Test
fun `rapid sequence preserves order`() = runBlocking {
    val input = JNativeHookKeyboardInput()
    val output = JNativeHookKeyboardOutput()
    val keys = mutableListOf<String>()
    val job = launch { input.keyPresses().take(3).collect { keys += it } }
    delay(100)
    output.postPress("A")
    output.postPress("B")
    output.postPress("C")
    delay(500)
    assertThat(keys).containsExactly("A", "B", "C")
    job.cancel()
}
```

---

## Layer 4: Full scenario replay (real platform, test windows)

### Architecture

```
┌──────────────────────────────────────────────────────────────┐
│  ReplayDriver                                                 │
│                                                               │
│  ┌────────────┐    ┌────────────────┐                         │
│  │ Recording  │───>│ Event scheduler│── posts real key events  │
│  │ (CSV file) │    │ (real Clock)   │── switches focus (real)  │
│  └────────────┘    └────────────────┘── paints test windows    │
│                                                               │
│  ┌──────────────────────────────────────────────────────────┐ │
│  │ Full stack (all real except game)                         │ │
│  │  Win32FocusManager + Win32ActiveWindowChecker             │ │
│  │  Win32Screen (reads from painted test windows)            │ │
│  │  JNativeHookKeyboard{Input,Output}                        │ │
│  │  Coordinator + BackgroundMacroRunner + AutoFlaskMacro      │ │
│  └──────────────────────────────────────────────────────────┘ │
│                                                               │
│  ┌──────────────┐                                             │
│  │ OutputLog    │◄── captures all keyboard output events      │
│  └──────────────┘   (compared against golden file)            │
└──────────────────────────────────────────────────────────────┘
```

### Test window as game substitute

Create a `JFrame("Path of Exile 2")` that paints flask-bar pixels at the correct screen positions. The `ReplayDriver` updates the painted colors from the recorded pixel timeline.

```kotlin
class GameSimWindow : JFrame("Path of Exile 2") {
    private val flaskColors = Array(5) { Color.BLACK }

    init {
        isUndecorated = true
        setSize(2560, 1440)
        setLocation(0, 0)
    }

    fun setFlaskColor(ix: Int, color: ScreenColor) {
        flaskColors[ix] = Color(color.red, color.green, color.blue)
        repaint()
    }

    override fun paint(g: Graphics) {
        super.paint(g)
        // Paint flask-bar pixels at the exact positions PoeFlasks checks
        PoeFlasks.X_COORDS.forEachIndexed { ix, x ->
            g.color = flaskColors[ix]
            g.fillRect(x - 2, PoeFlasks.Y_COORD - 2, 5, 5)  // Small square around check point
        }
    }
}
```

### Recording format

```csv
type,timestamp_ms,data
KEY_PRESS,0,W
PIXEL,50,"flask0=249:215:153,flask1=0:0:0,flask2=0:0:0,flask3=0:0:0,flask4=0:0:0"
PIXEL,100,"flask0=249:215:153,flask1=0:0:0,flask2=0:0:0,flask3=0:0:0,flask4=0:0:0"
KEY_RELEASE,500,W
FOCUS,600,Desktop
FOCUS,2000,Path of Exile 2
KEY_PRESS,2100,W
PIXEL,2150,"flask0=245:210:148,flask1=0:0:0,flask2=0:0:0,flask3=0:0:0,flask4=0:0:0"
```

### Golden output comparison

First run saves output log → `src/test/resources/golden/scenario-1.log`. Subsequent runs compare:

```
[50ms] bgMacro.flask: postPress("3")
[2200ms] bgMacro.flask: postPress("3")
```

Differences are flagged as test failures with a diff view.

### Scenarios

1. **Bg macros running → Alt+X → pick macro → idle**: Exercises focus stealing race (Bug 3). The JNativeHook keyboard output from bg macros might arrive during the focus steal window.

2. **Flask active → alt-tab → tab back → resume**: Win32Screen reads black pixels while alt-tabbed (game not rendering in test window background), then correct colors on tab-back.

3. **Rapid Alt+X double-tap**: Tests timing race between leader key detection and overlay state machine under real event delivery latency.

4. **Bg macro output during overlay focus**: Output suppression must work correctly when focus transitions happen via real Win32 APIs (not just fake `outputSuppressed = true`).

---

## Event logging (all layers)

```kotlin
data class LogEntry(
    val timestampMs: Long,
    val source: String,
    val message: String,
)

class EventLog {
    private val entries = Collections.synchronizedList(mutableListOf<LogEntry>())

    fun log(source: String, message: String, timestampMs: Long = System.currentTimeMillis()) {
        entries.add(LogEntry(timestampMs, source, message))
    }

    fun dump(): String = entries
        .sortedBy { it.timestampMs }
        .joinToString("\n") { "[${it.timestampMs}ms] ${it.source}: ${it.message}" }
}

class EventLogExtension : AfterTestExecutionCallback {
    override fun afterTestExecution(context: ExtensionContext) {
        if (context.executionException.isPresent) {
            val log = context.getStore(GLOBAL).get("eventLog", EventLog::class.java)
            System.err.println("=== Event Log ===")
            System.err.println(log?.dump() ?: "(no log)")
        }
    }
}
```

### Logging decorators

Wrap platform interfaces to log all calls:

```kotlin
class LoggingKeyboardOutput(
    private val delegate: KeyboardOutput,
    private val log: EventLog,
    private val source: String,
) : KeyboardOutput {
    override fun postPress(keyCode: String) {
        log.log(source, "postPress($keyCode)")
        delegate.postPress(keyCode)
    }
    override fun postRelease(keyCode: String) {
        log.log(source, "postRelease($keyCode)")
        delegate.postRelease(keyCode)
    }
}
```

Similar wrappers for `FocusManager`, `ActiveWindowChecker`, `Screen`.

---

## Cross-macro feedback (G4a)

### The problem

In production, JNativeHook hooks see all key events, including those injected by macros. So when auto-attack posts "W" via `KeyboardOutput`, flask macro's `keyStates()` flow (which listens via `KeyboardInput`) sees it. This is intentional (G4a).

### Layer 0 solution: LoopbackKeyboardOutput

```kotlin
class LoopbackKeyboardOutput(
    private val recording: FakeKeyboardOutput,
    private val loopback: FakeKeyboardInput,
) : KeyboardOutput {
    override fun postPress(keyCode: String) {
        recording.postPress(keyCode)
        loopback.emitPressSync(keyCode)  // Feed back into input
    }
    override fun postRelease(keyCode: String) {
        recording.postRelease(keyCode)
        loopback.emitReleaseSync(keyCode)
    }
}
```

### Layer 3+ solution: natural loopback

JNativeHook's `GlobalScreen.postNativeEvent()` fires the global hooks, so `JNativeHookKeyboardInput` naturally receives events posted by `JNativeHookKeyboardOutput`. No adapter needed.

### Test

```kotlin
@Test
fun `auto-attack W hold triggers flask macro`() = runTest {
    val harness = E2eTestHarness(this, loopback = true)
    harness.startBgMacros()
    harness.clock.advance(1100)  // past throttle

    // Toggle auto-attack (press D)
    harness.keyboard.emitPress("D")
    advanceTimeBy(100)

    // Auto-attack should post W → flask macro should detect W held → flask keys pressed
    advanceTimeBy(600)  // W hold duration (500ms) + margin
    assertThat(harness.keyboardOutput.events).anyMatch { it.keyCode in setOf("3", "4", "5") }
}
```

---

## Gradle setup

```kotlin
// macro-core/build.gradle.kts
plugins {
    `java-test-fixtures`
}
// testFixtures source set automatically exposes FakePlatform.kt classes

// macro-app/build.gradle.kts
dependencies {
    testImplementation(testFixtures(project(":macro-core")))
}

// Separate test tasks for Win32-only layers
tasks.test {
    useJUnitPlatform {
        excludeTags("win32", "jnativehook")
    }
}

tasks.register<Test>("testWin32") {
    useJUnitPlatform {
        includeTags("win32", "jnativehook")
    }
    // Single-threaded: these tests compete for focus/hooks
    maxParallelForks = 1
}
```
