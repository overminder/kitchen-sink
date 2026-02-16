# Gradle Module Setup

Status: done
Dependencies: none

## Description

Create a new Gradle submodule for the refactored code. This establishes clean separation from the legacy code — the new module must never depend on the old `com.gh.om.gamemacros` package.

## Acceptance Criteria

- [x] New module created (e.g., `:macro-core` or similar)
- [x] Module compiles independently
- [x] Test infrastructure set up (JUnit 5, AssertJ)
- [x] Kotlin coroutines dependency added
- [x] Root `settings.gradle.kts` updated to include the new module

## Notes

Keep dependencies minimal initially. Add platform-specific dependencies (JNA, JNativeHook) only when the platform abstraction layer is implemented.

The legacy module remains untouched and fully functional during migration.
