import CommitGolfCandidate.Memory
import CommitGolfCandidate.S6Tree

/-! One halfword store of zero at byte 30 of a stored 32-byte digest keeps the
digest's low 240 bits: the store changes only the digest's top doubleword. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem clear_offset_mod (address : Word) :
    byteOffset address = address.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change address.toNat &&& (2^3-1) = address.toNat % 2^3
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem clear_decomposition (address : Word) :
    alignToDword address + BitVec.ofNat 64 (byteOffset address) = address := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have disjoint : (address &&& ~~~7#64) &&& (address &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  have combined : (address &&& ~~~7#64) ||| (address &&& 7#64) = address := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint, combined]

private theorem clear_append_nat {highWidth lowWidth : Nat}
    (high : BitVec highWidth) (low : BitVec lowWidth) :
    (high ++ low).toNat = high.toNat * 2^lowWidth + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]

/-- Byte 6 of the doubleword at an aligned `top`. -/
theorem clear_half_address (top : Nat) (aligned : top % 8 = 0) :
    alignToDword (BitVec.ofNat 64 (top + 6)) = BitVec.ofNat 64 top ∧
    byteOffset (BitVec.ofNat 64 (top + 6)) = 6 := by
  have offset : byteOffset (BitVec.ofNat 64 (top + 6)) = 6 := by
    rw [clear_offset_mod, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, offset⟩
  have parts := clear_decomposition (BitVec.ofNat 64 (top + 6))
  rw [offset] at parts
  have joined : BitVec.ofNat 64 top + BitVec.ofNat 64 6 = BitVec.ofNat 64 (top + 6) := by
    rw [← BitVec.ofNat_add]
  have canceled := congrArg (fun value : Word => value - BitVec.ofNat 64 6)
    (parts.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using canceled

theorem clear_half_other (state : MachineState) (top : Nat) (aligned : top % 8 = 0)
    (query : Word) (other : query ≠ BitVec.ofNat 64 top) :
    (state.setHalfword (BitVec.ofNat 64 (top + 6)) 0).getMem query = state.getMem query := by
  simp only [MachineState.setHalfword, (clear_half_address top aligned).1]
  exact MachineState.getMem_setMem_ne other

private theorem replace_top_half (word : Word) :
    replaceHalfword word 3 0 = word &&& BitVec.ofNat 64 (2^48 - 1) := by
  unfold replaceHalfword
  simp only []
  have mask : (~~~(0xFFFF#64 <<< (3 * 16)) : Word) = BitVec.ofNat 64 (2^48 - 1) := by decide
  have zero : (BitVec.zeroExtend 64 (0 : BitVec 16) <<< (3 * 16) : Word) = 0 := by decide
  rw [mask, zero]
  exact BitVec.or_zero

theorem clear_half_top (state : MachineState) (top : Nat) (aligned : top % 8 = 0) :
    (state.setHalfword (BitVec.ofNat 64 (top + 6)) 0).getMem (BitVec.ofNat 64 top) =
      BitVec.ofNat 64 ((state.getMem (BitVec.ofNat 64 top)).toNat % 2^48) := by
  simp only [MachineState.setHalfword, (clear_half_address top aligned).1,
    (clear_half_address top aligned).2, MachineState.getMem_setMem_eq]
  generalize state.getMem (BitVec.ofNat 64 top) = word
  change replaceHalfword word 3 0 = _
  rw [replace_top_half]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2^48 - 1 < 2^64 by norm_num), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (show word.toNat % 2^48 < 2^64 by omega)]

/-- Clearing bytes 30 and 31 of a stored digest truncates it to 240 bits. -/
theorem read_digest_clear_top (state : MachineState) (address : Nat)
    (aligned : address % 8 = 0) (bounded : address + 32 < 2^64) :
    readBuffer (state.setHalfword (BitVec.ofNat 64 (address + 30)) 0) address 32 =
      s6Trunc (readBuffer state address 32) := by
  have topAligned : (address + 24) % 8 = 0 := by omega
  have at30 : address + 30 = address + 24 + 6 := by omega
  rw [at30, read_digest_words _ _ aligned, read_digest_words _ _ aligned,
    clear_half_top state (address + 24) topAligned]
  have keep (i : Nat) (small : i < 3) :
      (state.setHalfword (BitVec.ofNat 64 (address + 24 + 6)) 0).getMem
        (BitVec.ofNat 64 (address + 8*i)) = state.getMem (BitVec.ofNat 64 (address + 8*i)) := by
    apply clear_half_other state (address + 24) topAligned
    intro equal
    have numeric := congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at numeric
    omega
  have k0 := keep 0 (by decide)
  have k1 := keep 1 (by decide)
  have k2 := keep 2 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at k0 k1 k2
  rw [k0, k1, k2]
  have ha := (state.getMem (BitVec.ofNat 64 (address + 24))).isLt
  have hb := (state.getMem (BitVec.ofNat 64 (address + 16))).isLt
  have hc := (state.getMem (BitVec.ofNat 64 (address + 8))).isLt
  have hd := (state.getMem (BitVec.ofNat 64 address)).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [s6Trunc, clear_append_nat, BitVec.toNat_ofNat]
  generalize (state.getMem (BitVec.ofNat 64 (address + 24))).toNat = a at ha ⊢
  generalize (state.getMem (BitVec.ofNat 64 (address + 16))).toNat = b at hb ⊢
  generalize (state.getMem (BitVec.ofNat 64 (address + 8))).toNat = c at hc ⊢
  generalize (state.getMem (BitVec.ofNat 64 address)).toNat = d at hd ⊢
  rw [Nat.mod_eq_of_lt (show a % 2^48 < 2^64 by omega)]
  omega

/-- Words outside the cleared doubleword keep their contents. -/
theorem read_digest_clear_outside (state : MachineState) (top address : Nat)
    (aligned : top % 8 = 0) (addressAligned : address % 8 = 0)
    (bounded : address + 32 < 2^64) (topBound : top < 2^64)
    (outside : top + 8 ≤ address ∨ address + 32 ≤ top) :
    readBuffer (state.setHalfword (BitVec.ofNat 64 (top + 6)) 0) address 32 =
      readBuffer state address 32 := by
  apply read_digest_congr _ _ _ addressAligned
  intro i small
  apply clear_half_other state top aligned
  intro equal
  have numeric := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt topBound] at numeric
  omega

end CommitGolfCandidate
