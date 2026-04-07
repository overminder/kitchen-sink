-- Foundations: learning Lean 4 basics, SF/TPIL4-style exercises
-- Start here if you're new to Lean 4.

-- Coming from Coq: key orientation notes
-- • `theorem` ≈ `Lemma`/`Theorem`, `def` ≈ `Definition`
-- • `by` enters tactic mode (like `Proof.` ... `Qed.`)
-- • `#check`, `#eval`, `#print` are your REPL friends
-- • Lean 4 uses `·` (focused bullet) instead of `-`/`+`/`*`
-- • The infoview panel (Ctrl+Shift+Enter in VS Code) shows goals — your proof-state window

-- Example: a trivial theorem to verify your toolchain works
theorem and_comm_example (p q : Prop) (hp : p) (hq : q) : q ∧ p :=
  ⟨hq, hp⟩

-- Tactic style (more Coq-like):
theorem and_comm_example' (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  exact ⟨hq, hp⟩

#check and_comm_example
