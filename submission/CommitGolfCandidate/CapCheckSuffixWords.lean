import CommitGolfCandidate.CapCheckLoadedRecords

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckSuffixWords (input : CheckInput) (start : Nat) : List Digest :=
  List.ofFn (fun ordinal : Fin ((input.proof.length-start)/32) =>
    readBuffer (capProgram.initialState .check input)
      (capProgram.layout.proof+start+32*ordinal.val) 32)

theorem cap_check_suffix_words_length (input : CheckInput) (start : Nat) :
    (capCheckSuffixWords input start).length=(input.proof.length-start)/32 :=
  List.length_ofFn

theorem cap_check_suffix_words_slot (input : CheckInput) (start ordinal : Nat)
    (present : ordinal<(capCheckSuffixWords input start).length) :
    readBuffer (capProgram.initialState .check input)
      (capProgram.layout.proof+start+32*ordinal) 32=
      (capCheckSuffixWords input start)[ordinal] := by
  simp only [capCheckSuffixWords,List.getElem_ofFn]

theorem cap_check_suffix_words_prefix (input : CheckInput) (start : Nat)
    (admitted : input.proof.length≤capProgram.sizes.proof)
    (startBound : start ≤ input.proof.length) :
    (input.proof.drop start).take (32*(capCheckSuffixWords input start).length)=
      capDigestEncoding (capCheckSuffixWords input start) := by
  have countBound : 32*(capCheckSuffixWords input start).length≤
      (input.proof.drop start).length := by
    rw [cap_check_suffix_words_length,List.length_drop]
    omega
  apply List.ext_getElem
  · rw [List.length_take,Nat.min_eq_left countBound,cap_digest_encoding_length]
  · intro offset leftBound rightBound
    have inside : offset<32*(capCheckSuffixWords input start).length := by
      rw [cap_digest_encoding_length] at rightBound
      exact rightBound
    have originalInside : start+offset < input.proof.length := by
      rw [List.length_drop] at countBound
      omega
    have bytes := cap_slots_encoding (capProgram.initialState .check input)
      (capProgram.layout.proof+start) (capCheckSuffixWords input start)
      (cap_check_suffix_words_slot input start) offset inside
    rw [Nat.add_assoc,cap_check_input_proof_byte input (start+offset)
      admitted originalInside,
      List.getElem?_eq_getElem originalInside,Option.getD_some,
      List.getElem?_eq_getElem rightBound,Option.getD_some] at bytes
    simpa only [List.getElem_take,List.getElem_drop] using bytes

theorem cap_check_suffix_words_exact (input : CheckInput) (start : Nat)
    (admitted : input.proof.length≤capProgram.sizes.proof)
    (startBound : start ≤ input.proof.length) :
    input.proof.drop start =
      capDigestEncoding (capCheckSuffixWords input start) ++
        input.proof.drop (start+32*(capCheckSuffixWords input start).length) := by
  have dropped :
      (input.proof.drop start).drop (32*(capCheckSuffixWords input start).length)=
        input.proof.drop (start+32*(capCheckSuffixWords input start).length) :=
    List.drop_drop
  rw [←cap_check_suffix_words_prefix input start admitted startBound,←dropped,
    List.take_append_drop]

theorem cap_check_suffix_partial_length (input : CheckInput) (start : Nat)
    (startBound : start ≤ input.proof.length) :
    (input.proof.drop (start+32*(capCheckSuffixWords input start).length)).length<32 := by
  rw [List.length_drop,cap_check_suffix_words_length]
  have remainder := Nat.mod_lt (input.proof.length-start) (by decide : 0<32)
  have division := Nat.mod_add_div (input.proof.length-start) 32
  omega

end CommitGolfCandidate
