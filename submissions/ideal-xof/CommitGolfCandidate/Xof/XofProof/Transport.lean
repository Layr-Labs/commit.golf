import CommitGolfCandidate.Xof.XofProof.Witness

/-! Transport the compression Merkle collision witness to 256-bit XOF prefixes. -/

namespace CommitGolf.XofBaseline
open OracleComp OracleSpec Scheme
set_option maxRecDepth 100000

abbrev encodeTable := RandomOracleBaseline.encodeTable
local notation "encode" => RandomOracleBaseline.encode

lemma fixedRun_map_source (H : family.Realization) {α : Type}
    (c : OracleComp CompressionBaseline.family.world α) (S : CompressionBaseline.Table) (T : Table) :
    fixedRun H (simulateQ interface.worldImpl c) (encodeTable S ++ T) =
      (fun p => (p.1,encodeTable p.2 ++ T)) <$> CompressionBaseline.logRun (interface.project H) c S := by
  induction c using OracleComp.inductionOn generalizing S with
  | pure a => simp
  | query_bind q k ih =>
    cases q with
    | inl n =>
      simp only [simulateQ_bind, simulateQ_spec_query, MerkleAdapter.Interface.worldImpl]
      rw [fixedRun_coin, CompressionBaseline.logRun_coin_bind, map_bind]
      exact bind_congr fun u => ih u S
    | inr x =>
      simp only [simulateQ_bind, simulateQ_spec_query, MerkleAdapter.Interface.worldImpl]
      simp only [interface, bind_pure]
      rw [fixedRun_query, CompressionBaseline.logRun_fwd_bind]
      exact ih (digest H (encode x)) ((x,digest H (encode x))::S)

lemma good_encodeTable (S : CompressionBaseline.Table) (T : Table)
    (h : Good (encodeTable S ++ T)) : CompressionBaseline.Good S := by
  intro p hp p' hp' _ _ he
  apply RandomOracleBaseline.encode_injective
  apply h (encode p.1,p.2) (List.mem_append_left _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    (encode p'.1,p'.2) (List.mem_append_left _ (List.mem_map.mpr ⟨p',hp',rfl⟩)) he

lemma fixedRun_recheck (H : family.Realization) (claim : Claim)
    (hb : CompressionBaseline.merkle.Breaks (interface.project H) claim) (T : Table) :
    ∃ T', fixedRun H (simulateQ interface.worldImpl (CompressionBaseline.recheck claim)) T =
      pure ((),T') ∧ ¬Good T' ∧ T'.length ≤ T.length + 48 := by
  obtain ⟨S,hs,hbad,hlen⟩ := CompressionBaseline.logRun_recheck (interface.project H) claim hb []
  have hm := fixedRun_map_source H (CompressionBaseline.recheck claim) [] T
  simp only [encodeTable,RandomOracleBaseline.encodeTable,List.map_nil,List.nil_append,hs,map_pure] at hm
  refine ⟨encodeTable S ++ T,hm,fun h => hbad (good_encodeTable S T h),?_⟩
  simp only [encodeTable,RandomOracleBaseline.encodeTable,List.length_append,List.length_map]
  simp only [List.length_nil,zero_add] at hlen
  change S.length ≤ 48 at hlen
  omega
end CommitGolf.XofBaseline
