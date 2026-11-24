import CommitGolfCandidate.ChainedOpeningCodec

/-! Whole-packet boundaries hold for all position counts, not only the scored batch. -/
namespace CommitGolfCandidate.Chained.InteriorCodec
open CommitGolf SplitCodec

theorem accepted_packet_length (positions : Positions) (proof : Proof)
    (records : List Record) (footer : Footer positions)
    (accepted : unpackOpening positions proof=some (records,footer)) :
    proof.length=proofLength positions := by
  have canonical := opening_accepted positions proof records footer accepted
  rw [←canonical.2]
  exact encode_opening_length positions records footer canonical.1

theorem packet_length_range (positions : Positions) :
    482*positions.card≤proofLength positions ∧ proofLength positions≤482*positions.card+3776 := by
  have footerBound : footerBits (footerNodes positions)≤30208 := by
    unfold footerNodes
    split
    · simp [footerBits]
    · exact footer_bits_bound _
  unfold proofLength
  omega

theorem accepted_packet_range (positions : Positions) (proof : Proof)
    (records : List Record) (footer : Footer positions)
    (accepted : unpackOpening positions proof=some (records,footer)) :
    482*positions.card≤proof.length ∧ proof.length≤482*positions.card+3776 := by
  rw [accepted_packet_length positions proof records footer accepted]
  exact packet_length_range positions

theorem packet_length_source_fit (positions : Positions) : proofLength positions<2^33 := by
  have count : positions.card≤LENGTH := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ positions)
  have numeric : 482*LENGTH+3776<2^33 := by decide +kernel
  have bound := (packet_length_range positions).2
  omega

theorem record_slice_length (proof : Proof) (count index : Nat)
    (minimum : 482*count≤proof.length) (inside : index<count) :
    ((proof.drop (482*index)).take 482).length=482 := by
  simp only [List.length_take,List.length_drop]
  omega

theorem record_slice_tail_length (proof : Proof) (count index : Nat)
    (minimum : 482*count≤proof.length) (inside : index<count) :
    (((proof.drop (482*index)).take 482).drop 479).length=3 := by
  rw [List.length_drop,record_slice_length proof count index minimum inside]

theorem empty_packet_boundary (positions : Positions) (empty : positions.card=0)
    (proof : Proof) (records : List Record) (footer : Footer positions)
    (accepted : unpackOpening positions proof=some (records,footer)) : proof=[] := by
  have length := accepted_packet_length positions proof records footer accepted
  rw [proof_length_empty positions empty] at length
  exact List.length_eq_zero_iff.mp length

end CommitGolfCandidate.Chained.InteriorCodec
