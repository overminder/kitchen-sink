# Dagger DI Wiring

Status: done
Dependencies: macro-app-setup.md, platform-adapters.md

## Description

Dagger modules and component for compile-time dependency injection.

## Acceptance Criteria

- [x] `PlatformModule` provides all 6 platform interface bindings
- [x] `MacroModule` provides PoeInteractor, MultiRollLoop, LeaderKeyDetector
- [x] `AppComponent` exposes all needed dependencies
- [x] `./gradlew :macro-app:build` succeeds with Dagger code generation

## Notes

Uses `@Singleton` scope. `LeaderKeyDetector` is configured with leader key `Alt+X`.
