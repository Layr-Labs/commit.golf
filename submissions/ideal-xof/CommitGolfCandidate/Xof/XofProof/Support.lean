import CommitGolfCandidate.Xof.XofProof.Transport
import CommitGolfCandidate.Xof.XofProof.Game

/-! Relate the fixed-stream execution log to adversary and verifier query counts. -/

namespace CommitGolf.XofBaseline
open OracleComp OracleSpec Scheme
set_option maxRecDepth 100000

lemma fixedRun_counted_support (H : family.Realization) {α : Type}
    (c : OracleComp family.world α) (T : Table) (p : (α × Nat) × Table)
    (hp : p ∈ support (fixedRun H (counted c) T)) : p.2.length = T.length+p.1.2 := by
  induction c using OracleComp.inductionOn generalizing T p with
  | pure a =>
    simp only [counted_pure,fixedRun_pure,support_pure,Set.mem_singleton_iff] at hp
    subst p; simp
  | query_bind q k ih =>
    cases q with
    | inl n =>
      rw [counted_coin,fixedRun_coin] at hp
      simp only [support_bind,Set.mem_iUnion] at hp
      obtain ⟨u,_,hu⟩ := hp
      exact ih u T p hu
    | inr x =>
      rw [counted_query,fixedRun_query] at hp
      simp only [fixedRun,simulateQ_map,StateT.run_map,support_map] at hp
      obtain ⟨v,hv,rfl⟩ := hp
      have h := ih (IdealXof.eval H x) ((x.1,digest H x.1)::T) v hv
      simp only [List.length_cons] at h ⊢
      omega

lemma fixedRun_source_check (H : family.Realization) (c : OracleComp CompressionBaseline.HashSpec Bool)
    (T : Table) (p : Bool × Table)
    (hp : p ∈ support (fixedRun H (simulateQ interface.worldImpl (liftM c)) T)) :
    p.1 = ((interface.project H).eval c).1 ∧
      p.2.length = T.length + ((interface.project H).eval c).2 := by
  have hm := fixedRun_map_source H (liftM c) [] T
  simp only [encodeTable,RandomOracleBaseline.encodeTable,List.map_nil,List.nil_append] at hm
  rw [hm,support_map] at hp
  obtain ⟨v,hv,rfl⟩ := hp
  have hc := CompressionBaseline.map_logRun (interface.project H) (liftM c) []
  rw [CompressionBaseline.Hash.run_liftM] at hc
  simp only [map_pure,List.length_nil,zero_add,Prod.eta] at hc
  have hv' : (v.1,v.2.length) ∈ support ((fun p => (p.1,p.2.length)) <$>
      CompressionBaseline.logRun (interface.project H) (liftM c) []) := by
    rw [support_map]; exact ⟨v,hv,rfl⟩
  rw [hc,support_pure,Set.mem_singleton_iff] at hv'
  have h1 := congrArg Prod.fst hv'
  have h2 := congrArg Prod.snd hv'
  exact ⟨h1,by simp only [List.length_append,List.length_map]; omega⟩
end CommitGolf.XofBaseline
