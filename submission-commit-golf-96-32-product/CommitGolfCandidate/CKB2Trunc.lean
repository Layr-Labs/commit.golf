import CommitGolfCandidate.MemoryCore
import CommitGolfCandidate.Cut

/-! (CKB2 copy of CMHalf) A zero halfword store into bytes 30, 31 of an aligned 32-byte slot keeps the low 240 bits
of the stored digest: the slot then holds `widen (low240 digest)`. Ported from candT96 ParentRefinement. -/
namespace CommitGolfCandidate.CKB2Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem ckb2t_offset_mod (address : Word) : byteOffset address = address.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change address.toNat &&& (2^3-1) = address.toNat % 2^3
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem ckb2t_address_decomposition (address : Word) :
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

theorem ckb2t_nat_byte_offset (address : Nat) : byteOffset (BitVec.ofNat 64 address) = address % 8 := by
  rw [ckb2t_offset_mod, BitVec.toNat_ofNat]
  omega

theorem ckb2t_nat_align_dword (address : Nat) :
    alignToDword (BitVec.ofNat 64 address) = BitVec.ofNat 64 (8 * (address / 8)) := by
  have parts := ckb2t_address_decomposition (BitVec.ofNat 64 address)
  rw [ckb2t_nat_byte_offset] at parts
  have joined : BitVec.ofNat 64 (8 * (address / 8)) + BitVec.ofNat 64 (address % 8) =
      BitVec.ofNat 64 address := by
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  have canceled := congrArg (fun value : Word => value - BitVec.ofNat 64 (address % 8))
    (parts.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using canceled

/-- Clearing halfword 3 of the top word of a digest is `widen (low240 ·)`. -/
theorem ckb2t_trunc_words (w3 w2 w1 w0 : BitVec 64) :
    ((replaceHalfword w3 3 0 ++ w2) ++ w1) ++ w0 = widen (low240 (((w3 ++ w2) ++ w1) ++ w0)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [widen, low240, replaceHalfword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  rcases (by omega : i < 64 ∨ (64 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 192) ∨ (192 ≤ i ∧ i < 240) ∨
      (240 ≤ i ∧ i < 256)) with h | h | h | h | h
  · simp [h, show i < 240 by omega]
  · simp [show ¬ i < 64 by omega, show i - 64 < 64 by omega, show i < 240 by omega]
  · simp [show ¬ i < 64 by omega, show ¬ i - 64 < 64 by omega, show i - 64 - 64 < 64 by omega,
      show i < 240 by omega]
  · simp [show ¬ i < 64 by omega, show ¬ i - 64 < 64 by omega, show ¬ i - 64 - 64 < 64 by omega,
      show i - 64 - 64 - 64 < 48 by omega, show i - 64 - 64 - 64 < 64 by omega, show i < 240 by omega]
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 16 ∧ i = 240 + k := ⟨i - 240, by omega, by omega⟩
    simp [show ¬ 240 + k < 64 by omega, show ¬ 240 + k - 64 < 64 by omega,
      show ¬ 240 + k - 64 - 64 < 64 by omega, show ¬ 240 + k - 64 - 64 - 64 < 48 by omega,
      show 240 + k - 64 - 64 - 64 < 64 by omega, show ¬ 240 + k < 240 by omega,
      show 240 + k - 64 - 64 - 64 - 48 = k by omega]
    intro _
    have bits : ∀ k < 16, (65535#64).getLsbD k = true := by decide
    exact bits k hk

private theorem ckb2t_word_ne (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (different : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro same
  have := congrArg BitVec.toNat same
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact different this

/-- A zero halfword store into bytes 30, 31 of an aligned slot truncates its digest. -/
theorem ckb2t_trunc_store_digest (state : MachineState) (out : Nat) (aligned : out % 8 = 0)
    (bound : out + 32 ≤ 2^64) :
    readBuffer (state.setHalfword (BitVec.ofNat 64 (out+30)) 0) out 32 =
      widen (low240 (readBuffer state out 32)) := by
  rw [read_digest_words _ _ aligned, read_digest_words _ _ aligned]
  have align : alignToDword (BitVec.ofNat 64 (out+30)) = BitVec.ofNat 64 (out+24) := by
    rw [ckb2t_nat_align_dword]; congr 1; omega
  have pos : byteOffset (BitVec.ofNat 64 (out+30)) / 2 = 3 := by rw [ckb2t_nat_byte_offset]; omega
  have n0 := ckb2t_word_ne out (out+24) (by omega) (by omega) (by omega)
  have n8 := ckb2t_word_ne (out+8) (out+24) (by omega) (by omega) (by omega)
  have n16 := ckb2t_word_ne (out+16) (out+24) (by omega) (by omega) (by omega)
  simp only [MachineState.setHalfword, align, pos, MachineState.getMem_setMem_eq,
    MachineState.getMem_setMem_ne n0, MachineState.getMem_setMem_ne n8, MachineState.getMem_setMem_ne n16]
  exact ckb2t_trunc_words _ _ _ _

/-- The truncating store changes no byte outside its digest slot. -/
theorem ckb2t_trunc_store_outside (state : MachineState) (out address count : Nat)
    (aligned : out % 8 = 0) (outBound : out + 32 ≤ 2^64) (readBound : address + count ≤ 2^64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (state.setHalfword (BitVec.ofNat 64 (out+30)) 0) address count =
      readBuffer state address count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8*count))
  apply Finset.sum_congr rfl
  intro i hi
  have small := Finset.mem_range.mp hi
  have align : alignToDword (BitVec.ofNat 64 (out+30)) = BitVec.ofNat 64 (8*((out+30)/8)) :=
    ckb2t_nat_align_dword _
  have different : BitVec.ofNat 64 (8*((address+i)/8)) ≠ BitVec.ofNat 64 (8*((out+30)/8)) := by
    apply ckb2t_word_ne _ _ (by omega) (by omega)
    rcases separate with before | after <;> omega
  simp only [MachineState.setHalfword, MachineState.getByte, align, ckb2t_nat_align_dword (address+i),
    MachineState.getMem_setMem_ne different]

theorem ckb2t_set_halfword_mem_congr (left right : MachineState) (same : left.mem = right.mem)
    (address : Word) (half : BitVec 16) :
    (left.setHalfword address half).mem = (right.setHalfword address half).mem := by
  simp only [MachineState.setHalfword, MachineState.setMem, MachineState.getMem, same]

theorem ckb2t_half_offset (offset : Nat) (bounded : offset < 2048) :
    signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 offset := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega

theorem ckb2t_set_halfword_reg (t : MachineState) (address : Word) (half : BitVec 16) (reg : Reg) :
    (t.setHalfword address half).getReg reg = t.getReg reg := by
  cases reg <;> rfl

theorem ckb2t_set_halfword_pc (t : MachineState) (address : Word) (half : BitVec 16) :
    (t.setHalfword address half).pc = t.pc := rfl

/-- Clear the top two bytes of the 32-byte slot at `a`. -/
def ckb2ZeroTop (s : MachineState) (a : Nat) : MachineState := s.setHalfword (BitVec.ofNat 64 (a+30)) 0

end CommitGolfCandidate.CKB2Trunc
