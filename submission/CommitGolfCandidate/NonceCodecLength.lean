import CommitGolfCandidate.NonceCodec

/-! The compaction length law holds for arbitrary serialized input contents,
including adversarial nonce padding. Only the required record prefix length
is assumed; any following footer is retained unchanged. -/
namespace CommitGolfCandidate.NonceCodec
set_option maxHeartbeats 200000

theorem compact_length {α : Type} (count : Nat) (bytes : List α)
    (enough : 544*count ≤ bytes.length) :
    (compact count bytes).length=bytes.length-8*count := by
  induction count generalizing bytes with
  | zero => simp [compact]
  | succ count ih =>
    have first : 24 ≤ bytes.length := by omega
    have siblings : 512 ≤ (bytes.drop 32).length := by
      simp only [List.length_drop]
      omega
    have tail : 544*count ≤ (bytes.drop 544).length := by
      simp only [List.length_drop]
      omega
    simp only [compact, List.length_append, List.length_take,
      Nat.min_eq_left first, Nat.min_eq_left siblings, ih _ tail, List.length_drop]
    omega

end CommitGolfCandidate.NonceCodec
