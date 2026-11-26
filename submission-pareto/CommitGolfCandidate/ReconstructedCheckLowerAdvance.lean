import CommitGolfCandidate.ReconstructedCheckMemoryOps

namespace CommitGolfCandidate.Reconstruction.CheckLowerAdvance
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks
set_option maxHeartbeats 800000

/-- Two instructions advance the bit cursor and select the side of the next parent. -/
theorem positive (o : Oracle) (s : MachineState) (pc : s.pc=addr 246) :
    ∃ t, Segment o 2 s t [] ∧ t.pc=addr 248 ∧ t.getReg .x24=s.getReg .x5+s.getReg .x24 ∧
      t.getReg .x15 = (s.getReg .x23 &&& 1) ∧ (∀ r : Reg, r ≠ .x15 → r ≠ .x24 → t.getReg r = s.getReg r) ∧
      (∀ a,t.getMem a=s.getMem a) := by
  let u:=(s.setReg .x24 (s.getReg .x5+s.getReg .x24)).setPC (addr 247)
  let t:=(u.setReg .x15 (u.getReg .x23 &&& 1)).setPC (addr 248)
  have a : Segment o 1 s u []:=by
    apply plain _ _ _ _ (CheckMemoryOps.parsed (n:=246) (ins:=.base (.ADD .x24 .x5 .x24)) (by decide) s pc)
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,execInstrBr,pc,u];rfl
  have b : Segment o 1 u t []:=by
    apply plain _ _ _ _ (CheckMemoryOps.parsed (n:=247) (ins:=.base (.ANDI .x15 .x23 1)) (by decide) u rfl)
    rfl
  refine ⟨t,by simpa using compose a b,rfl,by rfl,by rfl,?_,fun _=>rfl⟩
  intro r n15 n24
  simp only [t,u,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ n15.symm,
    MachineState.getReg_setReg_ne _ _ _ _ n24.symm]

end CommitGolfCandidate.Reconstruction.CheckLowerAdvance
