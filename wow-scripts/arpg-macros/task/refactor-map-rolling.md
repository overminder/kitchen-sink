# Refactor Map Rolling Macro

Status: done
Dependencies: leader-key-detector.md, item-parser.md, map-scorer.md, reroll-provider.md, multi-roll-loop.md

## Description

The root goal of this refactoring effort. Migrate the map rolling macro (documented in `doc/map-rolling.md`) to the new module with full test coverage.

This task represents the original refactoring request. It depends on all component tasks and serves as the integration point where they come together into a working macro.

## Acceptance Criteria

- [x] Map rolling macro works end-to-end in the new module
- [x] Integration test covers the full flow (mocked platform APIs)
- [x] No dependencies on the old `com.gh.om.gamemacros` package
- [ ] Documentation updated if behavior changed

## Notes

See `doc/map-rolling.md` for the full behavioral spec.

Original requirements from the refactoring request:
- Incremental migration (one component at a time)
- TDD approach with unit tests on core components
- Platform APIs abstracted for testability (Windows-only, but mockable)
- New Gradle module, no dependencies on existing code
- Simple macro interface via dependency injection (no fancy DSL)
