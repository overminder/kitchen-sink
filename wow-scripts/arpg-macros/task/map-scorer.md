# Map Scorer

Status: done
Dependencies: item-parser.md, map-mod-database.md

## Description

Reimplement the map evaluation logic that decides whether a rolled map is "good enough". This includes:
- Reward scoring (weighted sum of quantity, pack size, scarab%, currency%, map%)
- Difficulty estimation (player damage taken × monster EHP multipliers)
- Bad mod blacklist checking

## Acceptance Criteria

- [x] Scoring profiles: SCARAB, MAP, INVITATION (configurable weights)
- [x] Composite scorer that picks best profile per map tier
- [x] Difficulty calculation from mod list
- [x] Difficulty ceiling check (early/mid/late game thresholds)
- [x] Bad mod detection (unconditional + conditional combinations)
- [x] Unit tests for scoring edge cases
- [x] Unit tests for difficulty calculation

## Notes

See `doc/map-rolling.md` for the scoring profile table and difficulty model description.

The scorer is pure logic — given a parsed item, return a score/difficulty/verdict. No platform dependencies.
