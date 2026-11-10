import CommitGolfCandidate.CapCheckWordSuffix

/-! The reached checker cursor is tied to complete words of the original
admitted proof and its exact partial tail. High-input framing preserves those
words after lower records, mark population and low-root writes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_loaded_word_suffix (input : CheckInput) (state : MachineState)
    (start : Nat) (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (startBound : start ≤ input.proof.length)
    (pointer : state.getReg .x25=BitVec.ofNat 64 (capProgram.layout.proof+start))
    (endPointer : state.getReg .x22=
      BitVec.ofNat 64 (capProgram.layout.proof+input.proof.length))
    (frame : CapHighBytes state (capProgram.initialState .check input)) :
    CapCheckWordSuffix state (capProgram.layout.proof+start)
      (capCheckSuffixWords input start) ((input.proof.length-start)%32) := by
  have wordsLength := cap_check_suffix_words_length input start
  have division := Nat.mod_add_div (input.proof.length-start) 32
  have address :
      capProgram.layout.proof+start+32*(capCheckSuffixWords input start).length+
          (input.proof.length-start)%32=
        capProgram.layout.proof+input.proof.length := by
    rw [wordsLength]
    omega
  have bounds := cap_check_loader_bounds input admitted
  have high : 22528≤capProgram.layout.proof := by
    norm_num [capProgram,capExperimental,candidate,layout,trapdoorBytes,
      LENGTH,LOG_LENGTH,LEAF_SIZE,DIGEST_BYTES]
  refine ⟨pointer,?_,by omega,?_,Nat.mod_lt _ (by decide),?_⟩
  · rw [address]
    exact endPointer
  · rw [address]
    exact bounds.1
  · intro ordinal present
    have wordBound : capProgram.layout.proof+start+32*ordinal+32≤2^64 := by
      rw [wordsLength] at present
      have finalBound := bounds.2.2
      omega
    rw [cap_high_bytes_read state (capProgram.initialState .check input) _ 32
      (by omega) wordBound frame]
    exact cap_check_suffix_words_slot input start ordinal present

theorem cap_check_loaded_partial_size (input : CheckInput) (start : Nat)
    (startBound : start ≤ input.proof.length) :
    (input.proof.drop (start+32*(capCheckSuffixWords input start).length)).length=
      (input.proof.length-start)%32 := by
  rw [List.length_drop,cap_check_suffix_words_length]
  have division := Nat.mod_add_div (input.proof.length-start) 32
  omega

end CommitGolfCandidate
