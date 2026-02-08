# PoeInteractor Interface/Impl Split + Test Improvements

Status: done
Dependencies: none

## Description

Split `PoeInteractor` into an interface and implementation to improve test boundaries.
Fix `MultiRollLoopTest` to use a fake instead of the real implementation, and add
coverage for the "reroll actually changes the item" scenario. Streamline DI with `@Inject`.

## Changes

### 1. Extract interface, rename class to `PoeInteractorImpl`

**`macro-core/.../core/PoeInteractor.kt`**:
- Extract `interface PoeInteractor` with 5 public methods:
  `getItemDescriptionAt`, `applyCurrencyTo`, `ctrlClick`, `ctrlShiftClick`, `getCurrencyCountAt`
- Rename the class to `PoeInteractorImpl`, implementing the interface
- Add `@Inject constructor` to `PoeInteractorImpl`

### 2. Add `FakePoeInteractor` to test fixtures

**`macro-core/.../core/FakePlatform.kt`**:
- Add `FakePoeInteractor : PoeInteractor` that:
  - `getItemDescriptionAt` returns from a configurable `var itemDescription: String?`
  - `applyCurrencyTo` records calls to a list (and optionally triggers an `onApplyCurrency` callback)
  - `ctrlClick`, `ctrlShiftClick` record calls
  - `getCurrencyCountAt` returns from a configurable `var currencyCount: Int`

### 3. Update macro-core consumers to use interface type

These files reference `PoeInteractor` as a type — they already depend on the interface
contract, so they just need the import to resolve (no code changes since the type name stays `PoeInteractor`):
- `MultiRollLoop.kt` line 31 — already `PoeInteractor`, now an interface (no change needed)
- `RerollProvider.kt` lines 17, 63 — same
- `CraftRerollProvider.kt` line 30 — same

### 4. Fix MultiRollLoopTest boundary

**`macro-core/.../core/MultiRollLoopTest.kt`**:
- Replace `keyboard`, `mouse` (FakeKeyboardOutput, FakeMouseOutput), `clipboard` (FakeClipboard)
  with a single `FakePoeInteractor`
- Keep `FakeMouseOutput` (MultiRollLoop also takes `MouseOutput` directly for `moveTo`)
- Keep `FakeClock`
- Remove `keyboard`, `clipboard` from setup — they were only needed for the real PoeInteractor

### 5. Add "reroll changes item" test

**`MultiRollLoopTest.kt`**:
- New test in `BasicRolling`:
  ```
  reroll changes item from bad to good
  ```
- `FakePoeInteractor.itemDescription` starts with a "bad" map description
- `FakeRerollProvider.applyTo` changes `FakePoeInteractor.itemDescription` to a "good" map
- Assert: `report.itemsRolled == 1`, `report.totalRerolls == 1`

### 6. Update RerollProviderTest and CraftRerollProviderTest

These tests legitimately test how RerollProvider implementations interact with
PoeInteractor (they verify specific mouse clicks happen). They should continue using the
real `PoeInteractorImpl` — just update the constructor call name.
- `RerollProviderTest.kt` line 72-73: `PoeInteractor(...)` → `PoeInteractorImpl(...)`
- `CraftRerollProviderTest.kt` line 39: same

### 7. Update DI in macro-app

**`MacroModule.kt`**:
- Remove the `poeInteractor()` `@Provides` method
- Add a `@Binds` method binding `PoeInteractor` to `PoeInteractorImpl`
  (requires converting to abstract class or splitting into abstract module)

**`AppComponent.kt`**:
- `fun poeInteractor(): PoeInteractor` — stays as-is (returns interface type)

## Acceptance Criteria

- [x] `PoeInteractor` is an interface; `PoeInteractorImpl` is the class
- [x] `FakePoeInteractor` exists in test fixtures
- [x] `MultiRollLoopTest` uses `FakePoeInteractor` — no keyboard/clipboard in its setup
- [x] New test covers "reroll changes item" scenario
- [x] `PoeInteractorTest` tests `PoeInteractorImpl` (rename only)
- [x] `RerollProviderTest` and `CraftRerollProviderTest` use `PoeInteractorImpl`
- [x] DI wiring uses `@Inject` + `@Binds` instead of manual `@Provides`
- [x] All tests pass (131 tests)
