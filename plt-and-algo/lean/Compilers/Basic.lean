-- Compilers: optimization algorithms with correctness proofs
-- Coming from a compiler/PL implementation background, this is where
-- you prove that your optimization passes preserve semantics.

-- Placeholder: a toy expression language to grow into
inductive Expr where
  | lit  : Int → Expr
  | add  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
  deriving Repr

def eval : Expr → Int
  | .lit n   => n
  | .add a b => eval a + eval b
  | .mul a b => eval a * eval b

-- Constant folding pass
def fold : Expr → Expr
  | .add (.lit a) (.lit b) => .lit (a + b)
  | .mul (.lit a) (.lit b) => .lit (a * b)
  | .add a b => .add (fold a) (fold b)
  | .mul a b => .mul (fold a) (fold b)
  | e => e

-- Correctness: folding preserves evaluation
theorem fold_correct : ∀ (e : Expr), eval (fold e) = eval e
  | .lit _ => rfl
  | .add (.lit a) (.lit b) => by simp [fold, eval]
  | .add (.lit a) (.add b c) => by simp [fold, eval, fold_correct (.add b c)]
  | .add (.lit a) (.mul b c) => by simp [fold, eval, fold_correct (.mul b c)]
  | .add (.add a b) c => by simp [fold, eval, fold_correct (.add a b), fold_correct c]
  | .add (.mul a b) c => by simp [fold, eval, fold_correct (.mul a b), fold_correct c]
  | .mul (.lit a) (.lit b) => by simp [fold, eval]
  | .mul (.lit a) (.add b c) => by simp [fold, eval, fold_correct (.add b c)]
  | .mul (.lit a) (.mul b c) => by simp [fold, eval, fold_correct (.mul b c)]
  | .mul (.add a b) c => by simp [fold, eval, fold_correct (.add a b), fold_correct c]
  | .mul (.mul a b) c => by simp [fold, eval, fold_correct (.mul a b), fold_correct c]
