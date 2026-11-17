import CommitGolfCandidate.CapWordCopy
import CommitGolfCandidate.HoistHelpers

/-! Copy instructions never read the PC as data. This frame transports only
their PC between relocated copies; registers, memory and load/store order
remain exact, including overlapping source/destination cases. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem pc_reg (state : MachineState) (pc : Word) (reg : Reg) (value : Word) :
    (state.setPC pc).setReg reg value = (state.setReg reg value).setPC pc := by
  cases reg <;> rfl

private theorem pc_mem (state : MachineState) (pc address value : Word) :
    (state.setPC pc).setMem address value = (state.setMem address value).setPC pc := rfl

private theorem load_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.LD destination source offset) =
      (execInstrBr state (.LD destination source offset)).setPC (pc+4) := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getMem_setPC,
    pc_reg, show (state.setPC pc).pc = pc from rfl, hoist_pc_pc]

private theorem store_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.SD destination source offset) =
      (execInstrBr state (.SD destination source offset)).setPC (pc+4) := by
  simp only [execInstrBr, MachineState.getReg_setPC, pc_mem,
    show (state.setPC pc).pc = pc from rfl, hoist_pc_pc]

theorem cap_word_copy_pc_frame (source destination : Reg)
    (sourceOffset destinationOffset : Nat) (state : MachineState) (pc : Word)
    (count : Nat) (bounded : count ≤ 8) :
    capWordCopyPrefix source destination sourceOffset destinationOffset (state.setPC pc) count =
      (capWordCopyPrefix source destination sourceOffset destinationOffset state count).setPC
        (pc+BitVec.ofNat 64 (4*count)) := by
  induction count with
  | zero =>
    rw [cap_word_copy_prefix_zero, cap_word_copy_prefix_zero]
    simp
  | succ count ih =>
    rw [cap_word_copy_prefix_succ _ _ _ _ _ count (by omega),
      cap_word_copy_prefix_succ _ _ _ _ _ count (by omega), ih (by omega)]
    have step (current : MachineState) (p : Word) :
        execInstrBr (current.setPC p)
            ((capWordCopyInstructions source destination sourceOffset destinationOffset)[count]?.getD .EBREAK) =
          (execInstrBr current
            ((capWordCopyInstructions source destination sourceOffset destinationOffset)[count]?.getD .EBREAK)).setPC (p+4) := by
      have bound : count ≤ 7 := by omega
      interval_cases count <;>
        simp only [capWordCopyInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some] <;>
        first | exact load_pc _ _ _ _ _ | exact store_pc _ _ _ _ _
    rw [step]
    congr 1
    rw [show 4*(count+1)=4*count+4 by omega, BitVec.ofNat_add, BitVec.add_assoc]
    rfl

end CommitGolfCandidate
