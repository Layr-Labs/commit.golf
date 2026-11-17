import CommitGolfCandidate.Compact.Opening
/-! Program-counter framing for path preparation and copying. Small instruction
congruences keep kernel checking from expanding nested symbolic memory. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem path_prepared_frame (s : MachineState) (pc : Word) :
    openingPathPreparedState (s.setPC pc)=(openingPathPreparedState s).setPC (pc+12) := by
  have expansion (s : MachineState) : openingPathPreparedState s =
      ([.XORI .x7 .x20 1,.SLLI .x7 .x7 5,.ADD .x23 .x9 .x7] : List Instr).foldl execInstrBr s := rfl
  simp [expansion,execInstrBr,MachineState.setPC,MachineState.setReg,
    MachineState.getReg,BitVec.add_assoc]

private theorem fast_load_pc (s : MachineState) (pc : Word)
    (rd rs : Reg) (offset : BitVec 12) :
    execInstrBr (s.setPC pc) (.LD rd rs offset)=
      (execInstrBr s (.LD rd rs offset)).setPC (pc+4) := by cases rd <;> rfl

private theorem fast_store_pc (s : MachineState) (pc : Word)
    (rd rs : Reg) (offset : BitVec 12) :
    execInstrBr (s.setPC pc) (.SD rd rs offset)=
      (execInstrBr s (.SD rd rs offset)).setPC (pc+4) := rfl

theorem path_copy_frame (s : MachineState) (pc : Word) :
    openingCopyState (s.setPC pc)=(openingCopyState s).setPC (pc+32) := by
  rw [opening_copy_expansion,opening_copy_expansion]
  simp only [List.foldl,fast_load_pc,fast_store_pc,BitVec.add_assoc]
  rfl

theorem path_advance_frame (s : MachineState) (pc : Word) :
    openingPathAdvancedState (s.setPC pc)=openingPathAdvancedState s := rfl

theorem path_frame_erasure (s : MachineState) (pc : Word) :
    openingPathState (s.setPC pc)=openingPathState s := by
  unfold openingPathState
  rw [path_prepared_frame,path_copy_frame,path_advance_frame]
end CommitGolfCandidate.Compact
