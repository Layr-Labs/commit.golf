import CommitGolf.Oracle.Family

/-! # Finite-domain compatibility

For finite-domain families, the shared state stores the sampled realization unchanged.
These lemmas connect shared execution to the original fixed-realization semantics. -/
namespace CommitGolf.OracleFamily
open OracleComp OracleSpec

/-- Whole-function sampling is available only for finite-domain families. -/
def HasFiniteDomain : OracleFamily → Prop
  | .permutation _ _ | .compression _ _ _ _ => True
  | .randomOracleFixedOutput _ _ => False
  | .sum F G => F.HasFiniteDomain ∧ G.HasFiniteDomain

instance decidableHasFiniteDomain (F : OracleFamily) : Decidable F.HasFiniteDomain :=
  match F with
  | .permutation _ _ => isTrue trivial
  | .compression _ _ _ _ => isTrue trivial
  | .randomOracleFixedOutput _ _ => isFalse id
  | .sum F G => @instDecidableAnd _ _ F.decidableHasFiniteDomain G.decidableHasFiniteDomain

/-- Independent uniform sampling of finite-domain instances. -/
def sample : (F : OracleFamily) → (h : F.HasFiniteDomain := by decide) → ProbComp F.Realization
  | .permutation n _, _ => IdealPermutation.sample n
  | .compression n k _ _, _ => IdealCompression.sample n k
  | .randomOracleFixedOutput _ _, h => False.elim h
  | .sum F G, h => do return (← F.sample h.1, ← G.sample h.2)

/-- Embed a finite-domain realization into the shared state. -/
def stateOf : (F : OracleFamily) → F.HasFiniteDomain → F.Realization → F.State
  | .permutation _ _, _, H => H
  | .compression _ _ _ _, _, H => H
  | .randomOracleFixedOutput _ _, h, _ => False.elim h
  | .sum F G, h, H => (F.stateOf h.1 H.1, G.stateOf h.2 H.2)

/-- The deterministic answer associated with a fixed realization. -/
def value (F : OracleFamily) (H : F.Realization) (q : F.Domain) : F.spec.Range q :=
  F.answer H (m := Id) q

lemma answer_eq_pure (F : OracleFamily) (H : F.Realization) {m : Type → Type}
    [Monad m] (q : F.Domain) : F.answer H (m := m) q = pure (F.value H q) := by
  induction F with
  | permutation => cases q <;> rfl
  | compression => rfl
  | randomOracleFixedOutput => rfl
  | sum F G ihF ihG => cases q with
    | inl q => exact ihF H.1 q
    | inr q => exact ihG H.2 q

lemma sharedAnswer_stateOf (F : OracleFamily) (h : F.HasFiniteDomain) (H : F.Realization)
    (q : F.Domain) :
    (F.sharedAnswer q).run (F.stateOf h H) = pure (F.value H q, F.stateOf h H) := by
  induction F with
  | permutation => cases q <;> rfl
  | compression => rfl
  | randomOracleFixedOutput => exact False.elim h
  | sum F G ihF ihG =>
    cases q with
    | inl q => simp [sharedAnswer, stateOf, ihF, value, answer]
    | inr q => simp [sharedAnswer, stateOf, ihG, value, answer]

lemma initialState_eq_sample (F : OracleFamily) (h : F.HasFiniteDomain) :
    F.initialState = (do let H ← F.sample h; return F.stateOf h H) := by
  induction F with
  | permutation => simp [initialState, sample, stateOf]
  | compression => simp [initialState, sample, stateOf]
  | randomOracleFixedOutput => exact False.elim h
  | sum F G ihF ihG => simp [initialState, sample, stateOf, ihF h.1, ihG h.2]

lemma checkShared_stateOf (F : OracleFamily) (h : F.HasFiniteDomain) (H : F.Realization)
    {α : Type} (c : OracleComp F.spec α) :
    (F.checkShared c).run (F.stateOf h H) = pure ((F.eval H c).1, F.stateOf h H) := by
  induction c using OracleComp.inductionOn with
  | pure a => simp [checkShared, eval]; rfl
  | query_bind q k ih =>
    simp [checkShared, eval, answer_eq_pure, StateT.run_bind, sharedAnswer_stateOf,
      checkShared] at ih ⊢
    exact ih (F.value H q)

lemma runShared_stateOf (F : OracleFamily) (h : F.HasFiniteDomain) (H : F.Realization)
    {α : Type} (c : OracleComp F.world α) :
    (F.runShared c).run (F.stateOf h H) = (do
      let result ← F.run H c
      return (result, F.stateOf h H)) := by
  induction c using OracleComp.inductionOn with
  | pure a => simp [runShared, run]; rfl
  | query_bind q k ih =>
    cases q with
    | inl q =>
      simp [runShared, run, callCost, map_eq_bind_pure_comp] at ih ⊢
      change (((liftM (unifSpec.query q) : StateT F.State ProbComp _) >>= fun u =>
        F.runShared (k u) >>= fun r => pure r) :
        StateT F.State ProbComp (α × Nat)).run (F.stateOf h H) = _
      simp only [bind_pure]
      change ((liftM (unifSpec.query q) : ProbComp _) >>= fun u =>
        (F.runShared (k u)).run (F.stateOf h H)) = _
      simp only [runShared, ih]
      simp only [Function.comp_def, bind_pure]
      change ((liftM (unifSpec.query q) : ProbComp _) >>= fun u =>
        F.run H (k u) >>= fun r => pure (r, F.stateOf h H)) =
        (((liftM (unifSpec.query q) : ProbComp _) >>= fun u => F.run H (k u)) >>=
          fun r => pure (r, F.stateOf h H))
      rw [bind_assoc]

    | inr q =>
      simp [runShared, run, callCost, answer_eq_pure, map_eq_bind_pure_comp] at ih ⊢
      change ((do
        let u ← F.sharedAnswer q
        let r ← F.runShared (k u)
        return (r.1, 1 + r.2)) : StateT F.State ProbComp (α × Nat)).run (F.stateOf h H) = _
      simp only [StateT.run_bind, sharedAnswer_stateOf, pure_bind]
      change ((F.runShared (k (F.value H q))).run (F.stateOf h H) >>= fun r =>
        pure ((r.1.1, 1 + r.1.2), r.2)) = _
      simp only [runShared, ih]
      simp only [Function.comp_def]
      change ((F.run H (k (F.value H q)) >>= fun r => pure (r, F.stateOf h H)) >>=
        fun r => pure ((r.1.1, 1 + r.1.2), r.2)) =
        ((F.run H (k (F.value H q)) >>= fun r => pure (r.1, 1 + r.2)) >>=
          fun r => pure (r, F.stateOf h H))
      simp only [bind_assoc, pure_bind]

end CommitGolf.OracleFamily
