import CommitGolfCandidate.OpeningOutput

/-! The opening's sorted positions and the checker's sorted dependent values use
the same order. The subtype proof attached to a value does not reorder its index. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Removing membership proofs from the sorted value indices gives the opening's
sorted position list. -/
theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

/-- The value at each checker ordinal belongs to exactly the index opened at that
ordinal by the submitted opening image. -/
theorem sorted_value_index (positions : Positions) (ordinal : Nat)
    (present : ordinal < positions.card) :
    (((positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present)).val).val =
      openingIndex positions ordinal := by
  have attachedBound : ordinal < (positions.attach.sort (fun i j => i.val ≤ j.val)).length := by
    simpa using present
  have positionBound : ordinal < (positions.sort (· ≤ ·)).length := by simpa using present
  have same := congrArg (fun list : List Index => list[ordinal]?) (sorted_value_indices positions)
  simp only [List.getElem?_map, List.getElem?_eq_getElem attachedBound,
    List.getElem?_eq_getElem positionBound, Option.map_some, Option.some.injEq] at same
  rw [same]
  simp only [openingIndex, dif_pos present]

private theorem read_word (state : MachineState) (address : Nat) (aligned : address%8 = 0) :
    readBuffer state address 8 = state.getMem (BitVec.ofNat 64 address) := by
  have slice := read_buffer_slice state address 32 0 8 (by decide)
  have word := read_digest_word state address 0 aligned (by decide)
  simpa only [Nat.mul_zero, Nat.add_zero] using slice.symm.trans word

/-- The checker's serialized index word is the same position selected by opening. -/
theorem check_input_position (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) :
    (submission.initialState .check input).getMem
      (BitVec.ofNat 64 (submission.layout.indices+8*ordinal)) =
        BitVec.ofNat 64 (openingIndex input.positions ordinal) := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card ≤ 16777216 := cardinal
  let index := (input.positions.sort (· ≤ ·))[ordinal]'(by simpa using present)
  have indexBound : index.val < 16777216 := index.isLt
  have bytes (offset : Nat) (inside : offset < 8) :
      (submission.initialState .check input).getByte
        (BitVec.ofNat 64 (submission.layout.indices+8*ordinal+offset)) =
          (BitVec.ofNat 64 index.val).extractLsb' (8*offset) 8 := by
    rw [initial_input_byte submission .check input _ (by change 5905584160+8*ordinal+offset < 2^64; omega)]
    have outside : ¬ (submission.layout.commitment ≤ submission.layout.indices+8*ordinal+offset ∧
        submission.layout.indices+8*ordinal+offset < submission.layout.commitment+(DIGEST_BITS+7)/8) := by
      change ¬ (4294971392 ≤ 5905584160+8*ordinal+offset ∧
        5905584160+8*ordinal+offset < 4294971424)
      omega
    have selected : submission.layout.indices ≤ submission.layout.indices+8*ordinal+offset ∧
        submission.layout.indices+8*ordinal+offset <
          submission.layout.indices+8*(input.positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      outside, decide_false, selected, and_self, decide_true]
    have quotient : (submission.layout.indices+8*ordinal+offset-submission.layout.indices)/8 = ordinal := by omega
    have remainder : (submission.layout.indices+8*ordinal+offset-submission.layout.indices)%8 = offset := by omega
    rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using present)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb', Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : index.val < 2^64)]
    rfl
  have decoded := read_serialized_slice (submission.initialState .check input)
    (BitVec.ofNat 64 index.val) (submission.layout.indices+8*ordinal) 0 8 (by
      simpa only [Nat.zero_add] using bytes)
  rw [read_word _ _ (by change (5905584160+8*ordinal)%8 = 0; omega)] at decoded
  change (submission.initialState .check input).getMem
    (BitVec.ofNat 64 (submission.layout.indices+8*ordinal)) =
      (BitVec.ofNat 64 index.val).extractLsb' 0 64 at decoded
  rw [BitVec.extractLsb'_eq_self] at decoded
  exact decoded.trans (by simp only [openingIndex, dif_pos present, index])

end CommitGolfCandidate
