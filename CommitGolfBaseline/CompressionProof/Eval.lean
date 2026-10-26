import CommitGolfBaseline.Compression

/-! # Running a computation against a fixed compression function

`simp` lemmas computing `Hash.eval` and `Hash.run` step by step. -/

namespace CommitGolf.CompressionBaseline.Hash
open OracleComp OracleSpec

variable (π : Hash)

@[simp] theorem family_run {α : Type} (c : OracleComp HashWorld α) :
    family.run π c = π.run c := by
  have ha : family.answer π (m := ProbComp) = π.answer (m := ProbComp) := by
    funext q
    rfl
  have hc : family.callCost = callCost := by funext q; cases q <;> rfl
  simp only [OracleFamily.run, run, counted, world, ha, hc]
  congr 2

@[simp] theorem family_eval {α : Type} (c : OracleComp HashSpec α) :
    family.eval π c = π.eval c := by
  have ha : family.answer π (m := Id) = π.answer (m := Id) := by
    funext q
    rfl
  simp only [OracleFamily.eval, eval, ha]
  congr 2

/-- The answer `π` gives to a compression function query. -/
def ans (t : Input) : HashSpec.Range t := π t

def fwd (x : Input) : OracleComp HashSpec Digest := (HashSpec.query x :)

@[simp] theorem eval_pure {α : Type} (a : α) :
    π.eval (pure a : OracleComp HashSpec α) = (a, 0) := by
  simp [eval]
  rfl

theorem eval_fwd_bind {α : Type} (x : Input) (k : Digest → OracleComp HashSpec α) :
    π.eval (fwd x >>= k) = ((π.eval (k (π x))).1, 1 + (π.eval (k (π x))).2) := by
  simp [eval, fwd]
  rfl

theorem eval_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    π.eval (oa >>= f) =
      ((π.eval (f (π.eval oa).1)).1, (π.eval oa).2 + (π.eval (f (π.eval oa).1)).2) := by
  simp [eval]
  rfl

theorem eval_query_bind {α : Type} (t : Input)
    (k : HashSpec.Range t → OracleComp HashSpec α) :
    π.eval ((liftM (HashSpec.query t) : OracleComp HashSpec _) >>= k) =
      ((π.eval (k (π.ans t))).1, 1 + (π.eval (k (π.ans t))).2) := by
  simp [eval, ans, answer]
  rfl

@[simp] theorem run_pure {α : Type} (a : α) :
    π.run (pure a : OracleComp HashWorld α) = pure (a, 0) := by
  simp [run]
  rfl

theorem run_bind {α β : Type} (oa : OracleComp HashWorld α) (f : α → OracleComp HashWorld β) :
    π.run (oa >>= f) = do
      let (a, n) ← π.run oa
      let (b, m) ← π.run (f a)
      return (b, n + m) := by
  simp [run, map_eq_bind_pure_comp]
  rfl

theorem run_hash_query_bind {α : Type} (t : Input)
    (k : HashSpec.Range t → OracleComp HashWorld α) :
    π.run ((liftM (HashWorld.query (Sum.inr t)) : OracleComp HashWorld _) >>= k) =
      (fun p => (p.1, 1 + p.2)) <$> π.run (k (π.ans t)) := by
  simp [run, counted, world, answer, ans, callCost]
  rfl

theorem run_liftM {α : Type} (c : OracleComp HashSpec α) :
    π.run (liftM c : OracleComp HashWorld α) = pure (π.eval c) := by
  induction c using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftM_bind, ← OracleComp.liftComp_eq_liftM (mx := liftM _), OracleComp.liftComp_query]
    change π.run ((liftM (HashWorld.query (Sum.inr t)) : OracleComp HashWorld _) >>= _) = _
    rw [run_hash_query_bind, ih, eval_query_bind]
    simp

end CommitGolf.CompressionBaseline.Hash
