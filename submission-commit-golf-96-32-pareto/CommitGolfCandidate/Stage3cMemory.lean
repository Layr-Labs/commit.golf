import CommitGolfCandidate.LateModel
import CommitGolfCandidate.Stage3cRngTile
import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.WriteMemoryCore

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem salt_address_pair (i : Nat) :
    saltAddress i = pairAddress (i/2) + (if i.testBit 0 then 16 else 0) := by
  simp only [saltAddress, pairAddress, Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
  split <;> simp_all <;> omega

theorem pair_address_valid (j : Nat) (hi : j < LENGTH/2) :
    pairAddress j % 8 = 0 ∧ pairAddress j + 40 ≤ MEMORY_BYTES := by
  change j < 8388608 at hi
  change (5905588224 + 184*j + 72) % 8 = 0 ∧ 5905588224 + 184*j + 72 + 40 ≤ 2^36
  omega

theorem disjoint_pairs {j k : Nat} (h : j < k) : pairAddress j + 40 ≤ pairAddress k := by
  unfold pairAddress
  omega

/-- A single RANDOM reply is recovered as the two overlapping salt windows. -/
theorem read_pair_salt (s : MachineState) (w : PairCoins) (i : Nat) :
    readBuffer (writeBits s (BitVec.ofNat 64 (pairAddress (i/2))) w)
      (saltAddress i) 24 = pairSalts w (i.testBit 0) := by
  rw [salt_address_pair]
  cases odd : i.testBit 0 <;> simp only [pairSalts, Bool.false_eq_true, if_false, if_true]
  · apply read_serialized_slice (value := w) (offset := 0)
    intro j hj
    simpa only [Nat.add_zero, Nat.zero_add, BitVec.ofNat_add] using
      write_bits_byte s (BitVec.ofNat 64 (pairAddress (i/2))) w j (by omega) (by decide)
  · apply read_serialized_slice (value := w) (offset := 16)
    intro j hj
    simpa only [Nat.add_assoc, BitVec.ofNat_add, BitVec.add_assoc] using
      write_bits_byte s (BitVec.ofNat 64 (pairAddress (i/2))) w (16+j) (by omega) (by decide)

/-- The later draw cannot overwrite either half of any previously filled pair. -/
theorem later_pair_preserves_salt (s : MachineState) (w : PairCoins) (i j : Nat)
    (past : i/2 < j) (inside : j < LENGTH/2) :
    readBuffer (writeBits s (BitVec.ofNat 64 (pairAddress j)) w) (saltAddress i) 24 =
      readBuffer s (saltAddress i) 24 := by
  have d := disjoint_pairs past
  have e := (pair_address_valid j inside).2
  change pairAddress j + 40 ≤ 2^36 at e
  have sep : saltAddress i + 24 ≤ pairAddress j := by rw [salt_address_pair]; split <;> omega
  apply write_bits_read_outside
  · change pairAddress j + 40 ≤ 2^64
    omega
  · omega
  · exact Or.inl sep

end CommitGolfCandidate.Chained.BinaryMachine
