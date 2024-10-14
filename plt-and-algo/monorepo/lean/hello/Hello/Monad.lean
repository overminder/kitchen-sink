-- Contract

structure MonadContract (m : Type → Type) [Monad m] where
  pure_left_id : ∀(v : α) (f : α → m β), bind (pure v) f = f v
  pure_right_id : ∀(v : m α), bind v pure = v
  bind_assoc : ∀(v : m α) (f : α → m β) (g : β → m χ),
    bind (bind v f) g = bind v (fun x => bind (f x) g)

-- Should probably be somewhat easier...
def optionMonadContract : MonadContract Option where
  pure_left_id := by
    intro α β v f
    rfl
  pure_right_id := by
    intro α v
    cases v
    ·  rfl
    ·  rfl
  bind_assoc := by
    intro α β χ v f g
    cases v
    ·  rfl
    ·  rfl

#print optionMonadContract.proof_3

def stateMonadContract : MonadContract (StateM σ) where
  pure_left_id := by
    intro α β v f
    rfl
  pure_right_id := by
    intro α v
    rfl
  bind_assoc := by
    intro α β χ v f g
    rfl

-- Hmm
def stateTMonadContract [inst: Monad m] (mc : MonadContract m): MonadContract (StateT σ m) where
  pure_left_id := by
    intro α β v f
    simp [bind, pure, StateT.pure]
    unfold StateT.pure StateT.bind
    simp
    unfold pure Applicative.toPure Monad.toApplicative
    sorry
  pure_right_id := by
    intro α v
    sorry
  bind_assoc := by
    intro α β χ v f g
    sorry
