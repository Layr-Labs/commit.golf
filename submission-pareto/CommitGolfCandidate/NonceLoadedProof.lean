import CommitGolfCandidate.NonceCompactBytes
import CommitGolfCandidate.NonceExpandedInput
import CommitGolfCandidate.CapInputBytes

/-! Entire trusted proof buffer, including arbitrary suffixes, as a byte list.
The expanded loader contains exactly the pure codec output. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem nonce_loaded_proof_bytes (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof) :
    nonceMemoryBytes (capProgram.initialState .check input) capProgram.layout.proof input.proof.length=
      input.proof := by
  apply List.ext_getElem
  · simp only [nonceMemoryBytes,List.length_map,List.length_range]
  · intro offset firstBound secondBound
    simp only [nonceMemoryBytes,List.getElem_map,List.getElem_range]
    rw [cap_check_input_proof_byte input offset admitted secondBound,
      List.getElem?_eq_getElem secondBound,Option.getD_some]

theorem nonce_loaded_expanded_proof (input : CheckInput) (words : Nat)
    (lengthEq : input.proof.length=536*input.positions.card+8*words)
    (admitted : (nonceExpandedInput input).proof.length ≤ capProgram.sizes.proof) :
    nonceMemoryBytes (capProgram.initialState .check (nonceExpandedInput input)) capProgram.layout.proof
      (544*input.positions.card+8*words)=
      NonceCodec.expand 0 input.positions.card
        (nonceMemoryBytes (capProgram.initialState .check input) capProgram.layout.proof
          (536*input.positions.card+8*words)) := by
  have enough : 536*input.positions.card ≤ input.proof.length := by omega
  have expandedLength:=nonce_expanded_input_length input enough
  have originalAdmitted : input.proof.length ≤ capProgram.sizes.proof := by omega
  have original:=nonce_loaded_proof_bytes input originalAdmitted
  have expanded:=nonce_loaded_proof_bytes (nonceExpandedInput input) admitted
  rw [lengthEq] at original
  have lengthExpanded : (nonceExpandedInput input).proof.length=544*input.positions.card+8*words := by omega
  rw [lengthExpanded] at expanded
  rw [original,expanded]
  rfl
end CommitGolfCandidate
