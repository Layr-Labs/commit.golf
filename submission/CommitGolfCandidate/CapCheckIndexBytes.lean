import CommitGolfCandidate.CapInputBytes
import CommitGolfCandidate.CapExperimentalABI

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

theorem cap_check_input_index (input : CheckInput) (offset : Nat) (bounded : offset < input.positions.card) :
    (capProgram.initialState .check input).getMem
      (BitVec.ofNat 64 (capProgram.layout.indices + 8 * offset)) =
        BitVec.ofNat 64 ((input.positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val := by
  let byteAt := fun address : Nat =>
    match (capProgram.inputBuffers .check input).find?
        (fun b => decide (b.address ≤ address ∧ address < b.address + b.length)) with
    | some b => b.byteAt (address - b.address)
    | none => if dataBase (capProgram.image .check) ≤ address then
        (capProgram.image .check).data[address - dataBase (capProgram.image .check)]?.getD 0
      else 0
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
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
        BitVec.ofNat 8 (((input.positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val /
          2 ^ (8 * j)) := by
    have before : ¬ (capProgram.layout.commitment ≤ capProgram.layout.indices + 8 * offset + j ∧
        capProgram.layout.indices + 8 * offset + j <
          capProgram.layout.commitment + (DIGEST_BITS + 7) / 8) := by
      norm_num [capProgram, capExperimental, candidate, layout, sizes, trapdoorBytes, LENGTH, LOG_LENGTH,
        LEAF_SIZE, DIGEST_BYTES, DIGEST_BITS]
      omega
    have inside : capProgram.layout.indices ≤ capProgram.layout.indices + 8 * offset + j ∧
        capProgram.layout.indices + 8 * offset + j <
          capProgram.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]
      omega
    have selected : (capProgram.inputBuffers .check input).find?
        (fun b => decide (b.address ≤ capProgram.layout.indices + 8 * offset + j ∧
          capProgram.layout.indices + 8 * offset + j < b.address + b.length)) =
          some (positionsBuffer capProgram.layout.indices input.positions) := by
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
        (BitVec.ofNat 8 (((input.positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val /
          2 ^ (8 * j))).toNat * 2 ^ (8 * j)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [bytes j (Finset.mem_range.mp hj)]
    _ = _ := index_word _

end CommitGolfCandidate
