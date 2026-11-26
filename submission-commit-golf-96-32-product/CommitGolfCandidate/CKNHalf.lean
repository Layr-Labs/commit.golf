import CommitGolfCandidate.MemoryCore
import CommitGolfCandidate.Cut

/-! CKN: the halfword store `sh x0,30(x12)` (x12 = 256) of the truncating compression adapter
clears the top 16 bits of the scratch digest at 256 (word 280). -/
namespace CommitGolfCandidate.CKNHalf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem ckn_set_halfword_reg (state : MachineState) (address : Word) (half : BitVec 16) (reg : Reg) :
    (state.setHalfword address half).getReg reg = state.getReg reg := by
  cases reg <;> rfl

theorem ckn_read_set_reg (state : MachineState) (reg : Reg) (value : Word) (address count : Nat) :
    readBuffer (state.setReg reg value) address count = readBuffer state address count := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem_setReg]

private theorem ckn_mask (w : Word) :
    replaceHalfword w 3 0 = w &&& 0x0000FFFFFFFFFFFF#64 := by
  unfold replaceHalfword
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp

theorem ckn_zero_top_shape (state : MachineState) :
    state.setHalfword (BitVec.ofNat 64 286) 0 =
      state.setMem (BitVec.ofNat 64 280) (state.getMem (BitVec.ofNat 64 280) &&& 0x0000FFFFFFFFFFFF#64) := by
  have a : alignToDword (BitVec.ofNat 64 286) = BitVec.ofNat 64 280 := by decide
  have b : byteOffset (BitVec.ofNat 64 286) / 2 = 3 := by decide
  unfold MachineState.setHalfword
  simp only [a, b, ckn_mask]

theorem ckn_zero_top_mem (state : MachineState) (address : Word) (outside : address ≠ 280) :
    (state.setHalfword (BitVec.ofNat 64 286) 0).getMem address = state.getMem address := by
  rw [ckn_zero_top_shape]
  exact MachineState.getMem_setMem_ne outside

private theorem ckn_top_clear (w3 w2 w1 w0 : Word) :
    ((w3 &&& 0x0000FFFFFFFFFFFF#64) ++ w2 ++ w1) ++ w0 = widen (low240 (((w3 ++ w2) ++ w1) ++ w0)) := by
  unfold widen low240
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_and, BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  interval_cases i <;> simp

/-- Clearing bytes 286, 287 truncates the scratch digest at 256. -/
theorem ckn_zero_top_digest (state : MachineState) :
    readBuffer (state.setHalfword (BitVec.ofNat 64 286) 0) 256 32 =
      widen (low240 (readBuffer state 256 32)) := by
  rw [read_digest_words _ _ (by decide), read_digest_words _ _ (by decide), ckn_zero_top_shape]
  simp only [Nat.reduceAdd]
  rw [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne (by decide),
    MachineState.getMem_setMem_ne (by decide), MachineState.getMem_setMem_ne (by decide)]
  exact ckn_top_clear _ _ _ _

end CommitGolfCandidate.CKNHalf
