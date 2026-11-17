import CommitGolfCandidate.CapCheckSuffixWords

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option autoImplicit false

theorem cap_check_encoded_suffix (input : CheckInput)
    (lowerWords suffix : List Digest)
    (encoded : input.proof=capDigestEncoding (lowerWords++suffix))
    (admitted : input.proof.length≤capProgram.sizes.proof) :
    capCheckSuffixWords input (32*lowerWords.length)=suffix ∧
      (input.proof.length-32*lowerWords.length)%32=0 := by
  have length : input.proof.length=32*(lowerWords.length+suffix.length) := by
    rw [encoded,cap_digest_encoding_length,List.length_append]
  have remaining : input.proof.length-32*lowerWords.length=32*suffix.length := by omega
  constructor
  · apply List.ext_getElem
    · rw [cap_check_suffix_words_length,remaining]
      omega
    · intro ordinal loadedBound suffixBound
      have indexBound : lowerWords.length+ordinal < (lowerWords++suffix).length := by
        rw [List.length_append]
        omega
      have slot := cap_check_encoded_slot input (lowerWords++suffix) []
        (by simpa only [List.append_nil] using encoded) admitted
        (lowerWords.length+ordinal) indexBound
      rw [←cap_check_suffix_words_slot input (32*lowerWords.length) ordinal loadedBound]
      rw [show capProgram.layout.proof+32*lowerWords.length+32*ordinal =
        capProgram.layout.proof+32*(lowerWords.length+ordinal) by omega,slot]
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
  · rw [remaining]
    omega

end CommitGolfCandidate
