import CommitGolfCandidate.Stage3cPtrLeafGeom

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxHeartbeats 2000000
set_option Elab.async false

private theorem pc_local : ∀ t : Fin 127,
    4123 + 12 * (t.val + 1) + (t.val + 1) / 16 + 2 * ((t.val + 1) / 32) =
      4123 + 12 * t.val + t.val / 16 + 2 * (t.val / 32) + 12 +
        (if (t.val + 1) % 32 = 0 then 3 else if (t.val + 1) % 16 = 0 then 1 else 0) := by
  decide

private theorem tail_small (k : Nat) (hk : k < LENGTH) (nz : (k + 1) % 128 ≠ 0) :
    tailCount k =
      if (k % 128 + 1) % 32 = 0 then 3 else if (k % 128 + 1) % 16 = 0 then 1 else 0 := by
  have hk' : k < 16777216 := by simpa [LENGTH, LOG_LENGTH] using hk
  have mod1 : (k + 1) % 128 = k % 128 + 1 := by omega
  have nz1 : k % 128 + 1 ≠ 0 := by omega
  have mod32 : (k + 1) % 32 = (k % 128 + 1) % 32 := by omega
  have mod16 : (k + 1) % 16 = (k % 128 + 1) % 16 := by omega
  rw [tailCount, mod1, ite_eq_right nz1, mod32, mod16]

/-- Inside a tile, the next leaf sits `12 + tailCount k` words after this one. -/
theorem pc_linear (k : Nat) (hk : k < LENGTH) (nz : (k + 1) % 128 ≠ 0) :
    leafPC (k + 1) = leafPC k + 12 + tailCount k := by
  have hk' : k < 16777216 := by simpa [LENGTH, LOG_LENGTH] using hk
  have lt : k % 128 < 127 := by omega
  have mod1 : (k + 1) % 128 = k % 128 + 1 := by omega
  have step := pc_local ⟨k % 128, lt⟩
  have tail := tail_small k hk nz
  simp only [leafPC, mod1, tail]
  exact step

/-- The back-edge lands on the first word of the same tile. -/
theorem pc_wrap (k : Nat) (z : (k + 1) % 128 = 0) : leafPC (k + 1) = 4123 := by
  simp only [leafPC, z, Nat.zero_div, Nat.mul_zero, Nat.add_zero]

theorem jal_back :
    pcAt 5677 + signExtend21 (BitVec.ofNat 21 2090936) = pcAt 4123 := by
  decide

theorem beq_skip :
    pcAt 5676 + signExtend13 (BitVec.ofNat 13 8) = pcAt 5678 := by
  decide

theorem last_leaf_pc : leafPC (LENGTH - 1) = 5660 := by
  simp only [leafPC, LENGTH, LOG_LENGTH]
  decide

end CommitGolfCandidate.Chained.BinaryMachine
