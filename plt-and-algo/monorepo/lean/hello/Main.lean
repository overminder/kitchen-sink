import «Hello»

-- Do notation
def main : IO Unit := do
  IO.println s!"Hello, {hello}!"
  -- ← needs a let, and can be the last statement
  let stdin ← IO.getStdin
  pure ()
