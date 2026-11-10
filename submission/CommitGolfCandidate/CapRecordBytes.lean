import CommitGolfCandidate.CapMemoryFrame

/-! Lower-record offsets in the exact cap byte transcript. Each record occupies
576 bytes, with its salt at offset zero and seventeen siblings in subsequent
32-byte slots. The memory frame transports these identities through low writes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem cap_transcript_slot (records : List CapLowerRecord) (ordinal slot : Nat)
    (present : ordinal < records.length) (inside : slot < 18) :
    (capLowerTranscript records)[18 * ordinal + slot]? =
      (capLowerEncoding records[ordinal])[slot]? := by
  induction records generalizing ordinal with
  | nil => simp at present
  | cons record rest ih =>
      cases ordinal with
      | zero =>
          simp only [capLowerTranscript, List.flatMap_cons, Nat.mul_zero,
            Nat.zero_add, List.getElem_cons_zero]
          exact List.getElem?_append_left (by rw [cap_lower_encoding_length]; exact inside)
      | succ ordinal =>
          have tailPresent : ordinal < rest.length := by simp at present; omega
          simp only [capLowerTranscript, List.flatMap_cons, List.getElem_cons_succ]
          rw [List.getElem?_append_right (by rw [cap_lower_encoding_length]; omega),
            cap_lower_encoding_length]
          have same : 18 * (ordinal + 1) + slot - 18 = 18 * ordinal + slot := by omega
          rw [same]
          exact ih ordinal tailPresent

theorem cap_transcript_salt (records : List CapLowerRecord) (ordinal : Nat)
    (present : ordinal < records.length) :
    (capLowerTranscript records)[18 * ordinal]?.getD 0 = records[ordinal].salt := by
  have slot := cap_transcript_slot records ordinal 0 present (by decide)
  simp only [Nat.add_zero, capLowerEncoding, List.getElem?_cons_zero] at slot
  rw [slot]
  rfl

theorem cap_transcript_sibling (records : List CapLowerRecord) (ordinal : Nat)
    (present : ordinal < records.length) (level : Fin 17) :
    (capLowerTranscript records)[18 * ordinal + (level.val + 1)]?.getD 0 =
      records[ordinal].sibling level := by
  have slot := cap_transcript_slot records ordinal (level.val + 1) present (by omega)
  simp only [capLowerEncoding, List.getElem?_cons_succ, List.getElem?_ofFn,
    level.isLt, ↓reduceDIte] at slot
  rw [slot]
  rfl

/-- This uses the actual input proof and a later framed machine state; it does
not assume that scratch or root memory still equals its initial contents. -/
theorem cap_framed_record_slot (input : CheckInput) (state : MachineState)
    (records : List CapLowerRecord) (suffix : Proof)
    (encoded : input.proof = capDigestEncoding (capLowerTranscript records) ++ suffix)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (frame : CapHighBytes state (capProgram.initialState .check input))
    (ordinal slot : Nat) (present : ordinal < records.length) (inside : slot < 18) :
    readBuffer state (capProgram.layout.proof + 576 * ordinal + 32 * slot) 32 =
      (capLowerEncoding records[ordinal])[slot]?.getD 0 := by
  have indexBound : 18 * ordinal + slot < (capLowerTranscript records).length := by
    rw [cap_lower_transcript_length]
    omega
  have slotValue := cap_transcript_slot records ordinal slot present inside
  have decoded : readBuffer state
      (capProgram.layout.proof + 32 * (18 * ordinal + slot)) 32 =
        (capLowerTranscript records)[18 * ordinal + slot] := by
    apply cap_encoding_read _ (capLowerTranscript records) suffix _ _ indexBound
    intro offset offsetBound
    erw [Nat.add_assoc, cap_framed_proof_byte input state _ admitted _ frame, encoded]
    rw [encoded, List.length_append, cap_digest_encoding_length]
    omega
  have address : capProgram.layout.proof + 32 * (18 * ordinal + slot) =
      capProgram.layout.proof + 576 * ordinal + 32 * slot := by omega
  rw [address] at decoded
  rw [decoded, ← slotValue, List.getElem?_eq_getElem indexBound, Option.getD_some]
end CommitGolfCandidate
