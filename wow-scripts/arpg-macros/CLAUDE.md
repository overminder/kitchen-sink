# CLAUDE.md

## Project Overview

Kotlin-based game macro automation framework, primarily for Path of Exile (POE). Uses coroutine-driven event loops with global keyboard/mouse hooks to automate game actions.

**Active refactoring**: Migrating from a single-module project into smaller Gradle modules (`macro-core`, `macro-overlay`, `macro-app`). The legacy `src/` root still contains code not yet migrated. See `task/done/` for completed migration tasks and `task/` for remaining work.

## Build & Run

```bash
./gradlew build       # Build all modules
./gradlew test        # Run tests (JUnit 5 + AssertJ)
./gradlew run         # Run the application
```

Gradle Kotlin DSL. Kotlin 2.0.10.

## Module Layout

| Module | Purpose |
|--------|---------|
| `macro-core` | Domain logic: item parsing, map scoring, crafting decisions, buff management, action combinators |
| `macro-overlay` | UI overlay (Compose Desktop) |
| `macro-app` | Application entry point, DI wiring (Dagger), platform adapters, macro definitions |
| `src/` (legacy root) | Not-yet-migrated code — being incrementally moved into the modules above |

## Architecture & Patterns

- **Coroutine-based**: Macros are `suspend` functions; input events exposed as `Flow<T>`
- **Platform abstraction**: `ScreenCommons.INSTANCE` factory, `enum class OS` detection. Primary: Windows (Win32/JNA). Secondary: macOS
- **Screen interaction**: Hardcoded positions for 2560x1440; color-based UI detection with Euclidean RGB distance
- **DI**: Dagger for wiring in `macro-app`

## Conventions

- `Poe*` prefix for POE-specific classes; `*Keeper` for buff managers; `*Commons` for utilities
- Sealed interfaces/classes for type-safe categorization
- `safeDelay()` for delays with random variance

## Testing

Tests in `macro-core/src/test/`. JUnit 5 + AssertJ. Focus on thread safety and concurrent correctness.

## Task Management

File-based task tracker in `task/`. See `task/README.md` for workflow.

### Task lifecycle

Each task has a `Status:` field (`todo`, `in-progress`, `done`):

1. **Exploration/Planning** — `todo`. Write the task description and detail plan in `task/attachment/`. No code changes.
2. **Implementation** — `in-progress`. Make code changes. Check off acceptance criteria.
3. **Done** — `done`. Build/tests pass, all criteria met.

### Planning workflow

Do NOT use Claude's built-in plan mode. Write plans directly to `task/` files:

1. **Research** — Explore the codebase, ask clarifications.
2. **Write plan** — Create the task file (and `task/attachment/` detail if needed). Present for review.
3. **Iterate** — User reviews and gives feedback. Revise until approved.
4. **Implement** — Only after user approves.

## IntelliJ MCP

**IMPORTANT: Always prefer IntelliJ MCP tools over CLI equivalents for code navigation and analysis.**

- **`find_files_by_name_keyword`** — Fast index-based file search by name substring (no globs).
- **`search_in_files_by_text/regex`** — Project-wide text search. Good for usage tracking / confirming dead code.
- **`get_file_problems`** — IntelliJ inspections without a full Gradle build. Use to quickly validate changes.
- **`get_symbol_info`** — Quick docs / type resolution at a cursor position.
- **`rename_refactoring`** — Context-aware rename across the project. Prefer over find-and-replace.
