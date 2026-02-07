# Macro App Gradle Module Setup

Status: done
Dependencies: none

## Description

Create the `macro-app` Gradle module with dependencies on macro-core, JNativeHook, JNA, Dagger (via KSP).

## Acceptance Criteria

- [x] `settings.gradle.kts` includes `macro-app`
- [x] `macro-app/build.gradle.kts` with KSP plugin and all dependencies
- [x] `./gradlew :macro-app:build` succeeds (empty module)
- [x] Tests pass

## Notes

Uses KSP for Dagger annotation processing (not kapt).
