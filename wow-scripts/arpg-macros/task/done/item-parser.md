# Item Parser

Status: done
Dependencies: gradle-module-setup.md

## Description

Reimplement the POE item description parser. This component takes the clipboard text from Ctrl+Alt+C (advanced item description) and extracts structured data: item class, rarity, explicit mods, quality bonuses.

This is pure parsing logic with no platform dependencies — it only needs the Gradle module to exist.

## Acceptance Criteria

- [x] Parses item class (map tier, currency, etc.)
- [x] Parses rarity (normal, magic, rare, unique)
- [x] Extracts explicit mods with tier info
- [x] Extracts quality bonuses (scarab%, currency%, pack%, etc.)
- [x] Handles T16, T16.5 (originator), and T17 map distinctions
- [x] Unit tests with real item description samples
- [x] Data classes for parsed item representation

## Notes

The parser is regex-based in the original. Consider whether the same approach or a more structured parser is appropriate.

Test with actual POE item descriptions captured from the game. These make good fixtures.
