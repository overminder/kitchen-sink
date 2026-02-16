# Macro Main Entry Point

Status: done
Dependencies: dagger-wiring.md

## Description

Main function and macro definitions that wire up map rolling and craft rolling macros using the Dagger component.

## Acceptance Criteria

- [x] `mapRollingMacro` triggered by leader key "11"
- [x] `craftRollingMacro` triggered by leader key "15"
- [x] `main()` registers JNativeHook, creates Dagger component, launches both macros
- [x] Currency slot constants defined
- [x] `./gradlew :macro-app:build` succeeds

## Notes

Cancellation deferred — macros run until leader key trigger stops naturally.
