import CommitGolfCandidate.Xof.RandomOracleProof.Lazy
namespace CommitGolf.RandomOracleBaseline
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
lemma counted_query {α : Type} (x : List Bool) (k : CompressionBaseline.Digest → OracleComp family.world α) :
    counted ((family.world.query (.inr x) : OracleComp family.world _) >>= k) =
      (family.world.query (.inr x) : OracleComp family.world _) >>= fun u =>
        (fun p => (p.1,1+p.2)) <$> counted (k u) := by
  simp [counted,OracleFamily.callCost]
  rfl

lemma run_counted {α : Type} (c : OracleComp family.world α) (T : Table) :
    run (counted c) T = (fun p => ((p.1,p.2.length-T.length),p.2)) <$> run c T := by
  induction c using OracleComp.inductionOn generalizing T with
  | pure a => simp [counted_pure]
  | query_bind q k ih =>
    cases q with
    | inl n =>
      rw [counted_coin,run_coin,run_coin,map_bind]
      exact bind_congr fun u => ih u T
    | inr x =>
      rw [counted_query,run_query,run_query,map_bind]
      apply bind_congr
      intro u
      simp only [map_eq_bind_pure_comp,Function.comp_def]
      simp only [run,simulateQ_bind,simulateQ_pure,StateT.run_bind,StateT.run_pure] at ih ⊢
      rw [ih]
      simp only [bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro p hp
      have h := length_le (k u) ((x,u)::T) p hp
      simp only [List.length_cons] at h ⊢
      congr 3
      omega

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

lemma run_counted_cache {α : Type} (c : OracleComp family.world α) (T : Table) :
    (fun p => ((p.1,p.2.length-T.length),toCache p.2)) <$> run c T =
      (family.runShared c).run (toCache T) := by
  have h := run_cache (counted c) T
  rw [counted_shared,run_counted] at h
  simpa only [Functor.map_map,Function.comp_def] using h
end CommitGolf.RandomOracleBaseline
