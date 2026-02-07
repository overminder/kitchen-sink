# CLAUDE.md

## Project Overview

Kotlin-based game macro automation framework, primarily for Path of Exile (POE). Uses coroutine-driven event loops with global keyboard/mouse hooks to automate game actions.

## Build & Run

```bash
./gradlew build       # Build
./gradlew test        # Run tests (JUnit 5 + AssertJ)
./gradlew run         # Run the application
```

Gradle Kotlin DSL build system. Kotlin 2.0.10.

## Key Dependencies

- **JNativeHook** - Global keyboard/mouse event hooks
- **Kotlinx Coroutines** - Async macro execution
- **JNA** - Windows/Mac native API access
- **Tess4j** - OCR for item text recognition

## Source Layout

```
src/main/kotlin/com/gh/om/gamemacros/
  Main.kt              # Entry point, registers hooks, launches macros
  GameSpecific.kt      # All game-specific macro definitions (POE, Diablo)
  GameGeneric.kt       # Buff management (SingleBuffKeeper, AlternatingBuffKeeper, etc.)
  KeyHooks.kt          # Keyboard input as Kotlin Flows
  MouseHooks.kt        # Mouse input as Kotlin Flows
  ActionCombinators.kt # Throttling, round-robin sequencing
  ScreenCommons.kt     # Platform-specific screen capture
  Win32Api.kt          # Windows native bindings
  MacApi.kt            # macOS native bindings
  complex/             # POE-specific automation
    poe.kt             # Core POE macros (bag dump, div cards, etc.)
    poecraft.kt        # Crafting automation
    poemap.kt          # Map rolling logic
    poemapdata.kt      # Map difficulty calculations
    PoeItem.kt         # Item data model (sealed interface)
    PoeItemParser.kt   # Regex-based item description parser
    multiroll.kt       # Multi-item rolling
    leadingKey.kt      # Leader key macros
  scratch/             # Experimental/scratch code
```

## Architecture & Patterns

- **Coroutine-based**: All macros are `suspend` functions running as concurrent coroutines
- **Flow-driven input**: Keyboard/mouse events exposed as `Flow<T>` streams
- **Platform abstraction**: `ScreenCommons.INSTANCE` factory, `enum class OS` detection
- **Thread safety**: `ConcurrentHashMap`, `AtomicReference`, explicit synchronization
- **Screen interaction**: Hardcoded positions for 2560x1440 resolution, color-based UI detection with Euclidean RGB distance
- **Safe delays**: `safeDelay()` adds ±10ms random variance

## Conventions

- `Poe*` prefix for POE-specific classes
- `*Keeper` suffix for buff/effect managers
- `*Commons` suffix for utility objects
- `is*` prefix for boolean checks
- Suspend functions for all async operations
- Sealed interfaces/classes for type-safe item categorization

## Testing

Tests in `src/test/kotlin/`. Uses JUnit 5 + AssertJ. Tests focus on thread safety and concurrent correctness (buff management, action throttling).

## Task Management

Use the file-based task tracker in `task/` for planning and tracking refactoring work. See `task/README.md` for workflow and conventions.

### Task lifecycle

Each task file has a `Status:` field (`todo`, `in-progress`, `done`). Keep it in sync across phases:

1. **Exploration/Planning** — Status stays `todo`. Write or refine the task description, acceptance criteria, and attachment (detail plan) in `task/attachment/`. No code changes yet.
2. **Implementation** — Set status to `in-progress`. Make code changes. Check off acceptance criteria as each is met.
3. **Done** — After build/tests pass and all criteria are checked, set status to `done`.

When working on a task, always update the task file status at each transition. If a task is split or new subtasks emerge, create new task files and update the dependency graph in `task/README.md`.

### Planning workflow

Do NOT use Claude's built-in plan mode. Instead, write plans directly to `task/` files:

1. **Research** — Explore the codebase, ask clarification questions as needed.
2. **Write plan** — Create the task file in `task/` (and detail plan in `task/attachment/` if needed). Present it to the user for review.
3. **Iterate** — User reviews the task file in-repo and gives feedback. Revise until approved.
4. **Implement** — Only after the user approves the plan.

## Platform Support

Primary: Windows (Win32 API via JNA). Secondary: macOS. Linux not implemented.

## IntelliJ MCP

IntelliJ provides MCP tools that are useful for code analysis. Prefer these over CLI equivalents when IntelliJ is running:

- **`find_files_by_name_keyword`** - Index-based file search by name substring. Faster than glob for finding files when you know part of the name. Does not support glob patterns or path matching.
- **`search_in_files_by_text/regex`** - Project-wide text search using IntelliJ's index. Good for usage tracking (e.g. confirming dead code).
- **`get_file_problems`** - Runs IntelliJ inspections on a file. Reports errors and warnings without a full Gradle build. Use this to quickly validate changes.
- **`get_symbol_info`** - Quick documentation / type resolution at a cursor position. Useful for checking what a symbol resolves to.
- **`rename_refactoring`** - Context-aware rename across the project. Prefer over find-and-replace for renaming symbols.
