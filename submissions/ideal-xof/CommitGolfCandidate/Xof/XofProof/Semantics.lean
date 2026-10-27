import CommitGolfCandidate.Xof.XofProof.Lazy

/-! The proof-only prefix log has the same observable distribution as the production
XOF handler. Deferred sampling removes the additional hidden prefix reads. -/

namespace CommitGolf.XofBaseline
open OracleComp OracleSpec
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
lemma simulate_readBits (x : IdealXof.Input) (start n : Nat) :
    simulateQ bitImpl (IdealXof.readBits (fun i =>
      (BitWorld.query (.inr (x,i)) : OracleComp BitWorld Bool)) start n) =
    IdealXof.readBits (fun i => Bits.randomOracle (x,i)) start n := by
  induction n generalizing start with
  | zero => simp [IdealXof.readBits]
  | succ n ih => simp [IdealXof.readBits,bitImpl,ih]

lemma expand_simulate {α : Type} (c : OracleComp family.world α) :
    simulateQ bitImpl (simulateQ expand c) =
      simulateQ (HasQuery.toQueryImpl (spec := unifSpec) (m := StateT Cache ProbComp) + family.sharedAnswer) c := by
  induction c using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,ih]
    congr 1
    cases q with
    | inl n => rfl
    | inr q => exact simulate_readBits q.1 0 q.2

lemma run_dropLog {α : Type} (c : OracleComp family.world α) (s : State) :
    (fun p => (p.1,p.2.1)) <$> run c s =
      (simulateQ bitImpl (simulateQ paddedExpand c)).run s.1 := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    cases q with
    | inl n =>
      rw [run_coin,map_bind]
      simp only [simulateQ_bind,simulateQ_spec_query,paddedExpand,bitImpl,
        QueryImpl.add_apply_inl,StateT.run_bind]
      have hn : (HasQuery.toQueryImpl (spec := unifSpec) (m := StateT Cache ProbComp) n).run s.1 =
          (fun u => (u,s.1)) <$> (unifSpec.query n : ProbComp _) := rfl
      rw [hn,bind_map_left]
      exact bind_congr fun u => ih u s
    | inr q =>
      rw [run_query,map_bind]
      simp only [simulateQ_bind,simulateQ_spec_query,paddedExpand,fillPrefix,expand,simulate_readBits,
        StateT.run_bind]
      change ((answer q).run s >>= _) = _
      simp only [answer,StateT.run,bind_assoc]
      apply bind_congr
      intro a
      rw [simulate_readBits]
      apply bind_congr
      intro b
      simp only [pure_bind]
      exact ih b.1 (b.2,(q.1,a.1)::s.2)

lemma run_shared {α : Type} (c : OracleComp family.world α) (s : State) :
    𝒮[Prod.fst <$> run c s] =
      𝒮[(simulateQ (HasQuery.toQueryImpl (spec := unifSpec) (m := StateT Cache ProbComp) +
        family.sharedAnswer) c).run' s.1] := by
  have h := congrArg (fun d => Prod.fst <$> d) (run_dropLog c s)
  simp only [Functor.map_map] at h
  rw [h]
  change 𝒮[bitRun (simulateQ paddedExpand c) s.1] = _
  rw [padding_preserves]
  unfold bitRun
  rw [expand_simulate]
end CommitGolf.XofBaseline
