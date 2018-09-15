data Race = Werewolf | Human

flipRace Werewolf = Human
flipRace Human = Werewolf

-- Nth player is what race
type Assertion = (Int, Race)

-- #, race
type Players = [Race]

raceAt :: Int -> Players -> Race
raceAt i rs = rs !! (i - 1)

flipAssertion :: Assertion -> Assertion
flipAssertion (i, r) = (i, flipRace r)

flipAssertions :: [Assertion] -> [Race] -> [Assertion]

genPlayers :: Int -> [Race]
genPlayers n = genPlayers' n 2

genPlayers' :: Int -> Int -> [Race]
genPlayers' n ww = if n == 0
  then if ww == 0
    then []
    else failed
  else if ww > 0
    then addWw ? addHuman
    else addHuman
 where
  addWw = Werewolf : genPlayers' (n - 1) (ww - 1)
  addHuman = Human : genPlayers' (n - 1) ww


