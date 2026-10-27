import CommitGolfCandidate.Xof.XofProof.Witness

/-! Count public XOF requests while leaving private random choices free. -/

namespace CommitGolf.XofBaseline
open OracleComp OracleSpec Scheme
set_option maxRecDepth 100000

def counted {α : Type} (c : OracleComp family.world α) : OracleComp family.world (α × Nat) :=
  (simulateQ ((HasQuery.toQueryImpl (spec := family.world)
    (m := OracleComp family.world)).withAddCost family.callCost) c).run

lemma counted_pure {α : Type} (a : α) : counted (pure a) = pure (a,0) := by
  simp [counted]; rfl
lemma counted_coin {α : Type} (n : Nat) (k : Fin (n+1) → OracleComp family.world α) :
    counted ((family.world.query (.inl n) : OracleComp family.world _) >>= k) =
      (family.world.query (.inl n) : OracleComp family.world _) >>= fun u => counted (k u) := by
  simp [counted,OracleFamily.callCost]
  rfl
lemma counted_query {α : Type} (x : family.Domain) (k : family.spec.Range x → OracleComp family.world α) :
    counted ((family.world.query (.inr x) : OracleComp family.world _) >>= k) =
      (family.world.query (.inr x) : OracleComp family.world _) >>= fun u =>
        (fun p => (p.1,1+p.2)) <$> counted (k u) := by
  simp [counted,OracleFamily.callCost]
  rfl

lemma counted_shared {α : Type} (c : OracleComp family.world α) :
    simulateQ (HasQuery.toQueryImpl (spec := unifSpec) (m := StateT family.State ProbComp) +
      family.sharedAnswer) (counted c) = family.runShared c := by
  induction c using OracleComp.inductionOn with
  | pure a => simp [counted_pure,OracleFamily.runShared]; rfl
  | query_bind q k ih =>
    cases q with
    | inl n =>
      rw [counted_coin]
      simp only [simulateQ_bind,simulateQ_spec_query]
      simp [OracleFamily.runShared,OracleFamily.callCost] at ih ⊢
      exact congrArg (fun f => (liftM (unifSpec.query n) : StateT family.State ProbComp _) >>= f) (funext ih)
    | inr x =>
      rw [counted_query]
      simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_map]
      simp [OracleFamily.runShared,OracleFamily.callCost] at ih ⊢
      simp only [ih]
      rfl

end CommitGolf.XofBaseline
