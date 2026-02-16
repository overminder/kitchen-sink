# Refactor Craft Rolling Macro

Status: done
Dependencies: craft-decision-maker.md, craft-methods.md, craft-reroll-provider.md

## Description

Root goal for migrating `PoeAltAugRegal.multiRoll` to macro-core. Depends on all craft component tasks. Once complete, the alt/aug/regal crafting pipeline will be fully testable and platform-decoupled.

## Acceptance Criteria

- [x] All craft component tasks done
- [x] `PoeAltAugRegal.multiRoll` can be rewritten to use macro-core's `MultiRollLoop` + `CraftRerollProvider`
- [x] No new dependencies on old `com.gh.om.gamemacros` package from macro-core

## Notes

The caller migration (rewriting `PoeAltAugRegal.multiRoll` itself) is optional for this task. The key deliverable is that macro-core has all the pieces needed.
