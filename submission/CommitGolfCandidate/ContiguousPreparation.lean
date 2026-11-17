import CommitGolfCandidate.ContiguousReference
import CommitGolfCandidate.ContiguousSalt

/-! The fixed return link permits contiguous salt copying to enter the same
reference leaf-ready registers directly. Only the physical PC is relocated. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem contiguous_load_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.LD destination source offset) =
      (execInstrBr state (.LD destination source offset)).setPC (pc + 4) := by
  cases destination <;> rfl

private theorem contiguous_store_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.SD destination source offset) =
      (execInstrBr state (.SD destination source offset)).setPC (pc + 4) := rfl

private theorem contiguous_addi_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.ADDI destination source offset)=
      (execInstrBr state (.ADDI destination source offset)).setPC (pc+4) := by
  cases destination <;> rfl

theorem contiguous_copy_pc (state : MachineState) (pc : Word) :
    commitCopyState (state.setPC pc) 46 = (commitCopyState state 46).setPC (pc + 32) := by
  rw [commit_copy_expansion, commit_copy_expansion]
  simp only [ite_true, List.foldl, contiguous_load_pc, contiguous_store_pc,contiguous_addi_pc]
  simp only [BitVec.add_assoc]
  rfl

theorem contiguous_salt_ready (state : MachineState) (messageBase : Word)
    (link : state.getReg .x1 = 4316) :
    (cursorSaltCopyState (cursorNormalize state messageBase 4456)).setPC 4484 =
      (cursorLeafFrame (commitPositionState state) messageBase).setPC 4484 := by
  change (cursorSaltCopyState (cursorLeafFrame (state.setPC 4456) messageBase)).setPC 4484 = _
  rw [cursor_salt_copy_frame, contiguous_copy_pc]
  have copiedLink : (commitCopyState state 46).getReg .x1 = 4316 := by
    rw [commit_copy_register state 46 .x1 (by decide)]
    exact link
  have sameLink : (commitCopyState state 46).setReg .x1 4316 = commitCopyState state 46 := by
    rw [← copiedLink]
    generalize commitCopyState state 46 = copied
    cases copied
    dsimp [MachineState.setReg, MachineState.getReg]
    congr 1
    funext reg
    cases reg <;> rfl
  simp only [commitPositionState, commitLeafCallState, sameLink]
  rfl

end CommitGolfCandidate
