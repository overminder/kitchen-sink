# Map Mod Database

Status: done
Dependencies: gradle-module-setup.md

## Description

Port the map mod descriptors (T16Mods, T17Mods) that define how each map modifier affects difficulty. Each mod has:
- Keywords for matching against item descriptions
- Variable index (which numeric value to extract)
- Difficulty multipliers (player damage taken, monster EHP)

## Acceptance Criteria

- [x] Data structure for mod descriptors
- [x] T16 mod definitions ported
- [x] T17 mod definitions ported
- [x] Keyword-based mod lookup function
- [x] Bad mod list (always annoying + conditional)
- [x] Unit tests for mod matching

## Notes

Consider loading from a data file (JSON) rather than hardcoding in Kotlin. The original has `poet16data.json` and `poet17data.json` — evaluate whether to use those or keep the Kotlin object definitions.

The mod list changes each POE league, so external data may be easier to maintain.
