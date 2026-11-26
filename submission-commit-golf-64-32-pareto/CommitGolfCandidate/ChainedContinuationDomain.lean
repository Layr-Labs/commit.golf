import CommitGolfCandidate.ChainedContinuationRun
import CommitGolfCandidate.ChainedEncoding

/-! Domain words prepared by the continuation image. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

private theorem register_store (s : MachineState) (address value : Word) (reg : Reg) :
    (s.setMem address value).getReg reg = s.getReg reg := by cases reg <;> rfl

private theorem register_zero (s : MachineState) : s.getReg .x0 = 0 := rfl

theorem header_stored_word (s : MachineState) (i : Fin 4) :
    (ordinaryPrefix s 1 8).getMem (s.getReg .x10+BitVec.ofNat 64 (32+8*i.val)) =
      match i.val with
      | 0 => (s.getReg .x17 <<< 3)-s.getReg .x17
      | 1 => 0
      | 2 => 0
      | _ => (1 : Word) <<< 63 := by
  fin_cases i <;>
    simp [ordinaryPrefix,continuationOps,execInstrBr,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.getMem_setPC,MachineState.getMem_setReg,
      register_store,register_zero,signExtend12,BitVec.add_right_inj]

structure DomainWords (s : MachineState) (buffer : Word) (h : Height) (j : Nat) : Prop where
  tag : s.getMem (buffer+32) = BitVec.ofNat 64 (7*h.val+j)
  zero0 : s.getMem (buffer+(40 : Word)) = 0
  zero1 : s.getMem (buffer+(48 : Word)) = 0
  flag : s.getMem (buffer+(56 : Word)) = BitVec.ofNat 64 (2^63)

theorem header_domain (s : MachineState) (h : Height)
    (height : s.getReg .x17 = BitVec.ofNat 64 h.val) :
    DomainWords (ordinaryPrefix s 1 8) (s.getReg .x10) h 0 := by
  have hh : h.val < 2^64 := by have := h.isLt; omega
  have tag : (s.getReg .x17 <<< 3)-s.getReg .x17 = BitVec.ofNat 64 (7*h.val) := by
    rw [height,BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 h.val*BitVec.ofNat 64 8-BitVec.ofNat 64 h.val = _
    rw [← BitVec.ofNat_mul,BitVec.ofNat_sub_ofNat_of_le _ _ hh (by omega)]
    congr 1
    omega
  constructor
  · have first := header_stored_word s (0 : Fin 4)
    change (ordinaryPrefix s 1 8).getMem (s.getReg .x10+32) =
      (s.getReg .x17 <<< 3)-s.getReg .x17 at first
    simpa using first.trans tag
  · exact header_stored_word s ⟨1,by decide⟩
  · exact header_stored_word s ⟨2,by decide⟩
  · exact header_stored_word s ⟨3,by decide⟩

end CommitGolfCandidate.Chained.Native
