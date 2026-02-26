# Snapshot Testing for Macro E2E

Status: todo
Dependencies: none

## Description

Add snapshot testing to capture and replay full IO traces of macro executions. When running a macro end-to-end with fake IO, record every IO call (input and output) as a serialized "snapshot". On subsequent test runs, replay the same inputs and assert the outputs match the saved snapshot.

## Feasibility Analysis

### What already exists

The codebase has excellent IO abstraction. All platform IO goes through interfaces defined in `Platform.kt`:

| Interface | Role | Fake in tests |
|---|---|---|
| `KeyboardOutput` | Post key press/release | `FakeKeyboardOutput` (records events) |
| `KeyboardInput` | Key event flows | `FakeKeyboardInput` (emits via SharedFlow) |
| `MouseOutput` | Move/click | `FakeMouseOutput` (records actions) |
| `MouseInput` | Click/motion flows | `FakeMouseInput` (emits via SharedFlow) |
| `Clipboard` | Get/set text | `FakeClipboard` (stores string) |
| `Screen` | Pixel color / capture | `FakeScreen` (configurable pixel map) |
| `Clock` | Time / delay | `FakeClock` (manual advance) |
| `ActiveWindowChecker` | Foreground check | `FakeActiveWindowChecker` |
| `ConsoleOutput` | Print text | (trivial to fake) |

Higher-level IO is also abstracted:
- `PoeInteractor` — game interaction (copy item text, apply currency, ctrl-click). `FakePoeInteractor` exists and records calls.
- `CurrencySlotsV2` — currency position mapping. Pure data, easy to stub.

### TabletRollingMacro dependency graph

```
TabletRollingMacro
├── MultiRollLoop
│   ├── PoeInteractor        ← IO (clipboard, keyboard, mouse, screen)
│   ├── MouseOutput          ← IO
│   └── Clock                ← IO
├── Poe2SortTablet.Factory
│   ├── PoeInteractor        ← IO
│   ├── MouseOutput          ← IO
│   ├── Clock                ← IO
│   └── PickDropSort         ← pure logic
├── ShouldContinueChecker
│   ├── ActiveWindowChecker  ← IO
│   ├── KeyboardInput        ← IO
│   └── GlobalMacroConfig    ← config
├── PoeInteractor            ← IO
├── CraftRerollProviderV2.Factory
│   ├── PoeInteractor        ← IO
│   └── CurrencySlotsV2      ← config/data
└── ConsoleOutput            ← IO
```

All leaves are either IO interfaces (all faked) or pure logic/config. **Full DI-level mocking is feasible today.**

### Feasibility verdict: HIGH

The architecture is already designed for testability:

1. **All IO is behind interfaces** — no static singletons, no direct system calls in `macro-core`.
2. **Fakes already exist** for every IO interface, with recording capability.
3. **DI via constructor injection** — `TabletRollingMacro` and all its transitive deps accept interfaces, no service locators.
4. **Deterministic control** — `FakeClock` eliminates timing nondeterminism. `FakeScreen` eliminates pixel-reading nondeterminism.
5. **The macro is a pure `suspend fun`** — no threads, no global state. `runTest` works.

### Design considerations

#### What a snapshot captures

A snapshot is a recorded E2E session. It has two parts:

1. **Stimuli (inputs)**: What the fake IO returns when the macro asks for it. Sequences of:
   - Clipboard reads (item descriptions returned at each `getItemDescriptionAt` call)
   - Screen pixel data for `getOccupiedBagSlots`
   - Currency counts for `getCurrencyCountAt`
   - `shouldContinue` sequence (when does the user "stop"?)

2. **Observations (outputs)**: What the macro did. Sequences of:
   - Mouse moves and clicks (positions, buttons)
   - Keyboard presses/releases
   - Clipboard writes (if any)
   - Console output text

A snapshot test replays the stimuli and asserts the observations match.

#### Recording level: PoeInteractor vs raw Platform

Two possible recording granularities:

| Level | Record at | Pros | Cons |
|---|---|---|---|
| **PoeInteractor** | `FakePoeInteractor` | Simpler snapshots, fewer entries, more readable. Changes to low-level key sequences don't break snapshots. | Doesn't test PoeInteractorImpl itself. |
| **Raw Platform** | `FakeKeyboard/Mouse/Clipboard/Screen` | Full E2E coverage including PoeInteractorImpl. | Snapshots are verbose and brittle to low-level timing/ordering changes. |

**Recommendation**: Record at the **PoeInteractor level**. The raw platform layer is already well-tested in `PoeInteractorImplTest`. Snapshot tests should focus on macro *logic* (decision-making, item evaluation, currency application order), not low-level input mechanics.

#### Snapshot format

Options:
- **Kotlin DSL** — snapshots are `.kt` files with a builder DSL. Type-safe, IDE-friendly, but can't be auto-generated easily.
- **JSON/YAML** — serialized trace files in `src/test/resources/`. Easy to auto-generate from a recording run, easy to diff. Needs a deserializer.
- **Inline string literals** — like the existing `goodMapDescription` / `badMapDescription` in `MultiRollLoopTest`. Simple but doesn't scale.

**Recommendation**: Start with **Kotlin DSL** since the project already uses this pattern in tests (see `MultiRollLoopTest` where `FakeRerollProvider.onApply` mutates state mid-run). A DSL keeps everything in Kotlin, avoids serialization complexity, and is the natural extension of the existing test style.

If snapshot volume grows large, graduate to JSON files later.

#### Sequencing challenge: stateful fakes

The key challenge is making fakes return **different values on successive calls**. For example, a tablet starts as a normal item, gets transmuted to magic, then augmented, etc. Each `getItemDescriptionAt` call must return the *current* item state.

This is already solved in the existing tests — `FakeRerollProvider.onApply` mutates `interactor.itemDescription` to simulate the item changing after a currency application. The same pattern extends naturally:

```kotlin
// Pseudocode for a snapshot-style test
val descriptions = listOf(normalTablet, magicTablet1Mod, magicTablet2Mods, rareTablet3Mods)
var callIndex = 0
fakeInteractor.onGetDescription = { descriptions[callIndex++] }
fakeInteractor.onApplyCurrency = { /* advance to next description */ callIndex++ }
```

A helper class (e.g., `ScriptedPoeInteractor`) that takes a sequence of (action, response) pairs would formalize this.

#### What's missing today

1. **`FakeConsoleOutput`** — trivial to add (just a `StringBuilder`).
2. **`FakeCurrencySlotsV2`** — trivial stub returning dummy `ScreenPoint`s.
3. **`FakeGlobalMacroConfig`** — trivial data class.
4. **Scripted `FakePoeInteractor`** — the current `FakePoeInteractor` returns a single fixed `itemDescription`. For snapshot tests, it needs to return a *sequence* of descriptions keyed by call order or item slot. Moderate effort.
5. **Scripted `FakeScreen`** for `getOccupiedBagSlots` — needs to return pixel data that makes slots appear occupied. The current `FakeScreen` supports this via `pixels` map, but the test would need to know the exact `PoeScreenConstants` grid positions and colors. Alternatively, mock at the `PoeInteractor` level where `getOccupiedBagSlots` returns a list of `ScreenPoint` directly.

### Risks

- **Snapshot brittleness**: If macro logic changes intentionally, all snapshots need updating. Mitigate by keeping snapshots small and focused (one scenario per snapshot).
- **PoeScreenConstants coupling**: If testing at the raw platform level, screen coordinates are hardcoded for 2560x1440. At the PoeInteractor level, this is abstracted away.
- **ShouldContinueChecker complexity**: Uses `StateFlow` + `combine` from `ActiveWindowChecker` polling + `KeyboardInput` events. For snapshot tests, simplest to bypass entirely and pass `shouldContinue = { true }` (already done in `MultiRollLoopTest`).

## Proposed approach

1. Add a `ScriptedPoeInteractor` (or enhance `FakePoeInteractor`) that accepts a sequence of item descriptions and currency counts, advancing state on each `applyCurrencyTo` call.
2. Test at the `PoeInteractor` level (not raw platform), using `FakePoeInteractor` for stimuli and asserting on its recorded calls for observations.
3. Write snapshot tests as Kotlin test functions with inline item descriptions (same style as `MultiRollLoopTest`).
4. Start with `TabletRollingMacro` as the first target since it's the simplest complete macro.
5. Each test scenario = one item rolling session with known inputs and expected output trace.

## Acceptance Criteria

- [ ] `ScriptedPoeInteractor` (or equivalent) supports sequenced item descriptions per slot
- [ ] `TabletRollingMacro` has at least 2 snapshot-style E2E tests covering:
  - A session where all tablets roll successfully
  - A session where currency runs out mid-roll
- [ ] Tests run via `./gradlew test` without real IO
- [ ] Snapshot assertions cover: which currencies were applied, in what order, to which slots, and final console output

## Notes

- The existing test infrastructure (`FakePlatform.kt`, `MultiRollLoopTest`, `PoeInteractorImplTest`) proves that the architecture supports this kind of testing. The main new work is the sequencing/scripting layer for `FakePoeInteractor`.
- Consider whether the `Poe2ChaoOnTablet` decision maker should also have its own unit tests (currently it has none). Snapshot tests would cover it transitively, but dedicated unit tests would be more focused.
