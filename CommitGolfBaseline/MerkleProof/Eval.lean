import CommitGolf

/-! # Running a computation against a fixed permutation

`simp` lemmas computing `Perm.eval` and `Perm.run` step by step. -/

namespace CommitGolf.Perm
open OracleComp OracleSpec

variable (π : Perm)

@[simp] theorem family_run {α : Type} (c : OracleComp World α) :
    OracleFamily.baseline.run π c = π.run c := by
  have ha : OracleFamily.baseline.answer π (m := ProbComp) = π.answer (m := ProbComp) := by
    funext q
    cases q <;> rfl
  have hc : OracleFamily.baseline.callCost = callCost := by funext q; cases q <;> rfl
  simp only [OracleFamily.run, run, counted, world, ha, hc]
  congr 2

@[simp] theorem family_eval {α : Type} (c : OracleComp PermSpec α) :
    OracleFamily.baseline.eval π c = π.eval c := by
  have ha : OracleFamily.baseline.answer π (m := Id) = π.answer (m := Id) := by
    funext q
    cases q <;> rfl
  simp only [OracleFamily.eval, eval, ha]
  congr 2

/-- The answer `π` gives to a permutation query. -/
def ans : (t : State ⊕ State) → PermSpec.Range t
  | .inl x => π x
  | .inr y => π.symm y

/-- A forward query `π x`, as a computation. -/
def fwd (x : State) : OracleComp PermSpec State := (PermSpec.query (Sum.inl x) :)

@[simp] theorem eval_pure {α : Type} (a : α) :
    π.eval (pure a : OracleComp PermSpec α) = (a, 0) := by
  simp [eval]
  rfl

theorem eval_fwd_bind {α : Type} (x : State) (k : State → OracleComp PermSpec α) :
    π.eval (fwd x >>= k) = ((π.eval (k (π x))).1, 1 + (π.eval (k (π x))).2) := by
  simp [eval, fwd]
  rfl

theorem eval_bind {α β : Type} (oa : OracleComp PermSpec α) (f : α → OracleComp PermSpec β) :
    π.eval (oa >>= f) =
      ((π.eval (f (π.eval oa).1)).1, (π.eval oa).2 + (π.eval (f (π.eval oa).1)).2) := by
  simp [eval]
  rfl

theorem eval_query_bind {α : Type} (t : State ⊕ State)
    (k : PermSpec.Range t → OracleComp PermSpec α) :
    π.eval ((liftM (PermSpec.query t) : OracleComp PermSpec _) >>= k) =
      ((π.eval (k (π.ans t))).1, 1 + (π.eval (k (π.ans t))).2) := by
  rcases t with x | y <;> simp [eval, ans, answer] <;> rfl

@[simp] theorem run_pure {α : Type} (a : α) :
    π.run (pure a : OracleComp World α) = pure (a, 0) := by
  simp [run]
  rfl

theorem run_bind {α β : Type} (oa : OracleComp World α) (f : α → OracleComp World β) :
    π.run (oa >>= f) = do
      let (a, n) ← π.run oa
      let (b, m) ← π.run (f a)
      return (b, n + m) := by
  simp [run, map_eq_bind_pure_comp]
  rfl

theorem run_perm_query_bind {α : Type} (t : State ⊕ State)
    (k : PermSpec.Range t → OracleComp World α) :
    π.run ((liftM (World.query (Sum.inr t)) : OracleComp World _) >>= k) =
      (fun p => (p.1, 1 + p.2)) <$> π.run (k (π.ans t)) := by
  rcases t with x | y <;> simp [run, counted, world, answer, ans, callCost] <;> rfl

theorem run_liftM {α : Type} (c : OracleComp PermSpec α) :
    π.run (liftM c : OracleComp World α) = pure (π.eval c) := by
  induction c using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftM_bind, ← OracleComp.liftComp_eq_liftM (mx := liftM _), OracleComp.liftComp_query]
    change π.run ((liftM (World.query (Sum.inr t)) : OracleComp World _) >>= _) = _
    rw [run_perm_query_bind, ih, eval_query_bind]
    simp

end CommitGolf.Perm
