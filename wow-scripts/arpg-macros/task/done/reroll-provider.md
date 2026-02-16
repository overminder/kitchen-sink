# Reroll Provider

Status: done
Dependencies: platform-abstraction.md, poe-interactor.md

## Description

Reimplement the currency application strategies for rerolling maps:
- Chaos Orb reroll (for rare items)
- Scour + Alchemy reroll (strips to normal, then makes rare)
- Tier-based hybrid (selects strategy based on map tier)

Each provider tracks remaining currency and stops when exhausted.

## Acceptance Criteria

- [x] `RerollProvider` interface with `hasMore()` and `applyTo()`
- [x] Chaos reroll implementation
- [x] Scour+Alch reroll implementation
- [x] Tier-based composite provider
- [x] Currency count checking (via clipboard item inspection)
- [x] Fuel limit support (max rerolls regardless of supply)
- [x] Unit tests with mocked mouse/keyboard

## Notes

Applying currency requires:
1. Right-click the currency in stash (picks it up)
2. Left-click the target item (applies it)

This needs the `PoeInteractor` abstraction for click operations.
