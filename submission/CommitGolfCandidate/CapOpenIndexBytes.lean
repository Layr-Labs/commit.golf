import CommitGolfCandidate.CapOpenRetainedInputs
import CommitGolfCandidate.CapExperimentalABI

/-! Sorted index words from the experimental opening loader. This specializes
 the retained loader argument to the cap images without identifying their
 initial stack pointer or instruction bytes with the older opening image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem index_word (index : Index) :
    BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
      (BitVec.ofNat 8 (index.val / 2 ^ (8 * j))).toNat * 2 ^ (8 * j)) =
        BitVec.ofNat 64 index.val := by
  congr 1
  have bounded : index.val < 16777216 := index.isLt
  norm_num [Finset.sum_range_succ, BitVec.toNat_ofNat]
  omega

/-- Reading an aligned serialized index recovers exactly the corresponding element
of the sorted position set, for every trapdoor and position set. -/
theorem cap_open_input_index (trapdoor : BitVec (8 * capProgram.sizes.trapdoor))
    (positions : Positions) (offset : Nat) (bounded : offset < positions.card) :
    (capProgram.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (capProgram.layout.indices + 8 * offset)) =
        BitVec.ofNat 64 ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val := by
  let byteAt := fun address : Nat =>
    match (capProgram.inputBuffers .opening (trapdoor, positions)).find?
        (fun b => decide (b.address ≤ address ∧ address < b.address + b.length)) with
    | some b => b.byteAt (address - b.address)
    | none => if dataBase (capProgram.image .opening) ≤ address then
        (capProgram.image .opening).data[address - dataBase (capProgram.image .opening)]?.getD 0
      else 0
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have addressNat : (BitVec.ofNat 64 (capProgram.layout.indices + 8 * offset)).toNat =
      capProgram.layout.indices + 8 * offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH,
      LEAF_SIZE, DIGEST_BYTES] at cardinal ⊢
    omega
  change BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
    (byteAt ((BitVec.ofNat 64 (capProgram.layout.indices + 8 * offset)).toNat + j)).toNat *
      2 ^ (8 * j)) = _
  rw [addressNat]
  have bytes (j : Nat) (hj : j < 8) :
      byteAt (capProgram.layout.indices + 8 * offset + j) =
        BitVec.ofNat 8 (((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val /
          2 ^ (8 * j)) := by
    have before : ¬ (capProgram.layout.trapdoor ≤ capProgram.layout.indices + 8 * offset + j ∧
        capProgram.layout.indices + 8 * offset + j <
          capProgram.layout.trapdoor + (8 * capProgram.sizes.trapdoor + 7) / 8) := by
      norm_num [capProgram, capExperimental, candidate, layout, sizes, trapdoorBytes, LENGTH, LOG_LENGTH,
        LEAF_SIZE, DIGEST_BYTES]
      omega
    have inside : capProgram.layout.indices ≤ capProgram.layout.indices + 8 * offset + j ∧
        capProgram.layout.indices + 8 * offset + j <
          capProgram.layout.indices + 8 * (positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]
      omega
    have selected : (capProgram.inputBuffers .opening (trapdoor, positions)).find?
        (fun b => decide (b.address ≤ capProgram.layout.indices + 8 * offset + j ∧
          capProgram.layout.indices + 8 * offset + j < b.address + b.length)) =
          some (positionsBuffer capProgram.layout.indices positions) := by
      simp only [Submission.inputBuffers, List.find?_cons, fixedBuffer]
      simp only [before, decide_false]
      simp only [positionsBuffer, inside]
      rfl
    simp only [byteAt, selected, positionsBuffer]
    have quotient : (capProgram.layout.indices + 8 * offset + j - capProgram.layout.indices) / 8 = offset := by omega
    have remainder : (capProgram.layout.indices + 8 * offset + j - capProgram.layout.indices) % 8 = j := by omega
    rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using bounded)]
  calc
    _ = BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
        (BitVec.ofNat 8 (((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val /
          2 ^ (8 * j))).toNat * 2 ^ (8 * j)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [bytes j (Finset.mem_range.mp hj)]
    _ = _ := index_word _


theorem cap_open_retained_index (floor : Nat)
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (bounded : ordinal < positions.card)
    (high : 22528 ≤ capProgram.layout.indices + 8*ordinal)
    (inside : capProgram.layout.indices + 8*ordinal + 32 ≤ floor)
    (aligned : (capProgram.layout.indices + 8*ordinal) % 8 = 0)
    (frame : CapOpenRetainedInputs floor
      (capProgram.initialState .opening (trapdoor, positions)) state) :
    state.getMem (BitVec.ofNat 64 (capProgram.layout.indices + 8*ordinal)) =
      BitVec.ofNat 64 ((positions.sort (· ≤ ·))[ordinal]'(by simpa using bounded)).val := by
  have same := cap_open_retained_read floor
    (capProgram.initialState .opening (trapdoor, positions)) state
    (capProgram.layout.indices + 8*ordinal) 32 high inside frame
  have word := congrArg (fun digest : Digest => digest.extractLsb' 0 64) same
  have words : state.getMem (BitVec.ofNat 64 (capProgram.layout.indices + 8*ordinal)) =
      (capProgram.initialState .opening (trapdoor, positions)).getMem
        (BitVec.ofNat 64 (capProgram.layout.indices + 8*ordinal)) := by
    simpa only [read_digest_word _ _ 0 aligned (by decide), Nat.mul_zero,
      Nat.add_zero] using word
  exact words.trans (cap_open_input_index trapdoor positions ordinal bounded)

end CommitGolfCandidate
