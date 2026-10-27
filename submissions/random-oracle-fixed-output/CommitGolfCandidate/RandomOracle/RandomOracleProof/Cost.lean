import CommitGolfCandidate.RandomOracle.RandomOracleProof.Lazy
namespace CommitGolf.CompressionBaseline
open OracleComp OracleSpec
lemma check_cost_le (H : Hash) (rt : Commitment) (ps : Positions) (vs : Values ps) (pf : Proof) :
    (H.eval (merkle.check rt ps vs pf)).2 ≤ LENGTH * LOG_LENGTH := by
  rw [eval_check]
  split
  · exact Nat.zero_le _
  rename_i hlen
  simp only [ne_eq,not_not] at hlen
  have hD : ((pf.toChunks DIGEST_BYTES).map Digest.ofBytes).length = (23+1)*ps.card := by
    rw [List.length_map,show DIGEST_BYTES = 31+1 from rfl,toChunks_eq_chunks,
      (chunks_length 31 (ps.card*LOG_LENGTH) pf
        (by rw [hlen]; simp [DIGEST_BYTES,LOG_LENGTH]; ring)).1]
    simp [LOG_LENGTH]; ring
  have hP := chunks_length 23 ps.card _ hD
  rw [← toChunks_eq_chunks,show 23+1 = LOG_LENGTH from rfl] at hP
  have hm : (((ordered ps).zip (paths pf)).map fun p => p.2.length) =
      List.replicate ((ordered ps).zip (paths pf)).length LOG_LENGTH := by
    rw [← List.map_const']
    apply List.map_congr_left
    intro p hp
    exact hP.2 p.2 (List.of_mem_zip hp).2
  rw [hm,List.sum_replicate,smul_eq_mul]
  have hc : ps.card ≤ LENGTH := by
    have h := Finset.card_le_univ ps
    simpa only [Fintype.card_fin] using h
  have hz : ((ordered ps).zip (paths pf)).length ≤ ps.card := by
    rw [List.length_zip,length_ordered]; exact min_le_left _ _
  exact Nat.mul_le_mul_right _ (hz.trans hc)
end CommitGolf.CompressionBaseline
