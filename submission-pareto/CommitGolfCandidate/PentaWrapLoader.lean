import CommitGolfCandidate.PentaWrapMemory
import CommitGolfCandidate.PentaWrapCode

/-! Register file and index words of the check loader, for any submission with the penta layout. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 (memoryView wordAddress)

/-- Registers set by the check loader: `sp`, the six buffers, the count and the proof length. -/
def loaderReg (count length : Nat) : Reg → Word
  | .x2 => BitVec.ofNat 64 (2^36)
  | .x10 => BitVec.ofNat 64 4096
  | .x11 => BitVec.ofNat 64 4294971392
  | .x12 => BitVec.ofNat 64 4294971424
  | .x13 => BitVec.ofNat 64 6375350304
  | .x14 => BitVec.ofNat 64 6509568096
  | .x15 => BitVec.ofNat 64 10804535392
  | .x16 => BitVec.ofNat 64 count
  | .x17 => BitVec.ofNat 64 length
  | _ => 0

theorem loader_reg {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (r : Reg) :
    (sub.initialState .check input).getReg r = loaderReg input.positions.card input.proof.length r := by
  have base := data_base_value lay
  have l := lay.layout
  cases r <;> simp [Submission.initialState, loaderReg, base, l, inputCount,
    inputProofLength, Riscv.initialMachine, MachineState.getReg] <;> rfl

theorem loader_pc (sub : Submission) (input : CheckInput) :
    (sub.initialState .check input).pc = BitVec.ofNat 64 4096 := rfl

/-- Word `796918788 + o` of the loader holds the `o`-th sorted position. -/
theorem index_word {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (o : Nat)
    (present : o < input.positions.card) :
    memoryView (sub.initialState .check input) (796918788 + o) =
      BitVec.ofNat 64 (sortedIndex input.positions o) := by
  have cardinal : input.positions.card ≤ 16777216 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact this
  let index := (input.positions.sort (· ≤ ·))[o]'(by simpa using present)
  have indexBound : index.val < 16777216 := index.isLt
  have named : sortedIndex input.positions o = index.val := by
    unfold sortedIndex
    rw [List.getElem?_eq_getElem (by simpa using present)]
    rfl
  have hc : sub.layout.commitment = 4294971392 := by rw [lay.layout]
  have hi : sub.layout.indices = 6375350304 := by rw [lay.layout]
  have state := sub.initialState .check input
  have bytes (offset : Nat) (inside : offset < 8) :
      (sub.initialState .check input).getByte (BitVec.ofNat 64 (6375350304+8*o+offset)) =
        (BitVec.ofNat 64 index.val).extractLsb' (8*offset) 8 := by
    rw [initial_input_byte sub .check input _ (by omega)]
    have outside : ¬ (4294971392 ≤ 6375350304+8*o+offset ∧ 6375350304+8*o+offset < 4294971392+(DIGEST_BITS+7)/8) := by
      have : (DIGEST_BITS+7)/8 = 32 := rfl
      omega
    have selected : 6375350304 ≤ 6375350304+8*o+offset ∧
        6375350304+8*o+offset < 6375350304+8*(input.positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]; omega
    unfold inputByte
    simp only [Submission.inputBuffers, hc, hi, List.find?_cons, fixedBuffer, positionsBuffer,
      outside, decide_false, selected, and_self, decide_true]
    have quotient : (6375350304+8*o+offset-6375350304)/8 = o := by omega
    have remainder : (6375350304+8*o+offset-6375350304)%8 = offset := by omega
    rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using present)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb', Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : index.val < 2^64)]
    rfl
  have decoded := read_serialized_slice (sub.initialState .check input)
    (BitVec.ofNat 64 index.val) (6375350304+8*o) 0 8 (by simpa only [Nat.zero_add] using bytes)
  have slice := read_buffer_slice (sub.initialState .check input) (6375350304+8*o) 32 0 8 (by decide)
  have word := read_digest_word (sub.initialState .check input) (6375350304+8*o) 0 (by omega) (by decide)
  have aligned : readBuffer (sub.initialState .check input) (6375350304+8*o) 8 =
      (sub.initialState .check input).getMem (BitVec.ofNat 64 (6375350304+8*o)) := by
    simpa only [Nat.mul_zero, Nat.add_zero] using slice.symm.trans word
  rw [aligned] at decoded
  change (sub.initialState .check input).getMem (BitVec.ofNat 64 (6375350304+8*o)) =
    (BitVec.ofNat 64 index.val).extractLsb' 0 64 at decoded
  rw [BitVec.extractLsb'_eq_self] at decoded
  unfold memoryView wordAddress
  rw [show 8*(796918788+o) = 6375350304+8*o by omega, decoded, named]

/-- The sorted positions are increasing. -/
theorem sorted_index_mono (positions : Positions) (a b : Nat) (le : a ≤ b) (present : b < positions.card) :
    sortedIndex positions a ≤ sortedIndex positions b := by
  have sorted := Finset.pairwise_sort positions (· ≤ ·)
  have la : a < (positions.sort (· ≤ ·)).length := by rw [Finset.length_sort]; omega
  have lb : b < (positions.sort (· ≤ ·)).length := by rw [Finset.length_sort]; omega
  have rel := sorted.rel_get_of_le (a := ⟨a, la⟩) (b := ⟨b, lb⟩) (by simpa using le)
  unfold sortedIndex
  rw [List.getElem?_eq_getElem la, List.getElem?_eq_getElem lb]
  simpa using rel

end TwoPermutationPrototype.PentaWrap
