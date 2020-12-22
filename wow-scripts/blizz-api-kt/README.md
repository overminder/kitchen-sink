### Synopsis

Access Blizzard API to optimize my char, by planning my next dungeon to run.

### Planning

1. Use Blizzard API to get item stats from dungeons.

   1.1. Problem: Bapi doesn't support bonus (e.g. scaling ilvl).
        All the SL dungeon items are 158 ilevel.

        Read simc source to see how they do ilevel scaling. 

### Links

- To create/manage Blizzard API clients:
  https://develop.battle.net/access/clients

- API doc (credentials flow):
  https://develop.battle.net/documentation/guides/using-oauth/client-credentials-flow

- API doc (WoW data):
  https://develop.battle.net/documentation/world-of-warcraft/game-data-apis

- Another WoW API client in Java:
  https://github.com/chalverson/wowjavaapi
