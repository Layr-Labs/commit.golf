import CommitGolfCandidate.NonceCheckScheme
import CommitGolfCandidate.NonceOldProofCanonical
import CommitGolfCandidate.NonceHidingSecurity

namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

def nonceOldSchemeProof (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : Proof :=
  if positions.card=0 then [] else capOpenLoadedBytes trapdoor positions

theorem nonce_old_scheme_opening (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    capProgram.scheme.opening trapdoor positions=pure (nonceOldSchemeProof trapdoor positions) := by
  unfold nonceOldSchemeProof
  split
  · exact cap_open_empty_scheme_bytes trapdoor positions ‹_›
  · exact cap_open_nonempty_scheme_bytes trapdoor positions (by omega)

theorem nonce_honest_check_eq (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (root : Commitment) (values : Values positions) :
    nonceCompressedProgram.scheme.check root positions values
      (NonceCodec.compact positions.card (nonceOldSchemeProof trapdoor positions))=
      capProgram.scheme.check root positions values (nonceOldSchemeProof trapdoor positions) := by
  by_cases empty : positions.card=0
  · have proofEq : nonceOldSchemeProof trapdoor positions=[] := if_pos empty
    rw [proofEq,empty,NonceCodec.compact]
    have valid : NonceCheckValid ⟨root,positions,values,[]⟩ := by
      unfold NonceCheckValid
      simp only [empty,List.length_nil,Nat.mul_zero,Nat.zero_mod,Nat.zero_add,le_refl]
      decide
    have checkEq:=nonce_check_scheme_valid ⟨root,positions,values,[]⟩ valid
    simpa only [nonceExpandedInput,empty,NonceCodec.expand] using checkEq
  · have proofEq : nonceOldSchemeProof trapdoor positions=capOpenLoadedBytes trapdoor positions := if_neg empty
    rw [proofEq]
    have fullLength:=cap_open_loaded_bytes_length trapdoor positions
    have capacity:=cap_open_loaded_bytes_capacity trapdoor positions
    have enough : 544*positions.card ≤ (capOpenLoadedBytes trapdoor positions).length := by omega
    have compactLength:=NonceCodec.compact_length positions.card (capOpenLoadedBytes trapdoor positions) enough
    let input : CheckInput:=⟨root,positions,values,NonceCodec.compact positions.card (capOpenLoadedBytes trapdoor positions)⟩
    have valid : NonceCheckValid input := by
      unfold NonceCheckValid
      change (NonceCodec.compact positions.card (capOpenLoadedBytes trapdoor positions)).length%8=0 ∧
        536*positions.card ≤ (NonceCodec.compact positions.card (capOpenLoadedBytes trapdoor positions)).length ∧
        (NonceCodec.compact positions.card (capOpenLoadedBytes trapdoor positions)).length+8*positions.card ≤ 13421772800
      have maximum : (capOpenLoadedBytes trapdoor positions).length ≤ 13421772800 := capacity
      rw [compactLength]
      omega
    have checkEq:=nonce_check_scheme_valid input valid
    change nonceCompressedProgram.scheme.check root positions values _=
      capProgram.scheme.check root positions values
        (NonceCodec.expand 0 positions.card (NonceCodec.compact positions.card (capOpenLoadedBytes trapdoor positions))) at checkEq
    rw [nonce_old_proof_roundtrip] at checkEq
    exact checkEq
end CommitGolfCandidate
