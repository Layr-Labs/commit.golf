import CommitGolfCandidate.TruncWireStages
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 120000

def Preserved (r : Reg) := r≠.x6 ∧ r≠.x17 ∧ r≠.x18 ∧ r≠.x19 ∧ r≠.x28

private theorem ptrKept (b f : Bool) (s : MachineState) (r : Reg) (p : Preserved r) :
    (pointers b f s).getReg r=s.getReg r := by
  simp only [pointers,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.2.2.1)]

private theorem regKept (b f : Bool) (pc : Word) (s : MachineState) (r : Reg) (p : Preserved r) :
    (regStep b f pc s).getReg r=s.getReg r := by
  have m : (moved b f s).getReg r=(before b f s).getReg r := listKept _ _ _ p.1
  unfold regStep
  simp only [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.2.2.2)]
  cases b <;> simp only [ready,before,Bool.false_eq_true,ite_true,ite_false,ptrKept _ _ _ _ p,m]

private theorem loopKept (f : Bool) (pc : Word) (s : MachineState) (r : Reg) (p : Preserved r) (k : Nat) :
    ((regStep true f pc)^[k] s).getReg r=s.getReg r := by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply',regKept _ _ _ _ _ p,ih]

private theorem initKept (s : MachineState) (r : Reg) (p : Preserved r) : (init true s).getReg r=s.getReg r := by
  simp only [init,initOps,ite_true,List.foldl,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.2.1),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.2.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.2.2.2)]
private theorem setZero (s : MachineState) (v : Word) : s.setReg .x0 v=s := rfl
private theorem endKept (s : MachineState) (r : Reg) (p : Preserved r) : (endState true s).getReg r=s.getReg r := by
  simp only [endState,endOps,ite_true,List.foldl,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.2.1),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.2.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.2.2.2),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.1),setZero]
private theorem resetKept (s : MachineState) (r : Reg) (p : Preserved r) : (reset s).getReg r=s.getReg r := by
  simp only [reset,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p.2.2.2.2)]

theorem unpackedKeeps (s : MachineState) (r : Reg) (h : Preserved r) :
    (unpackedEnd s).getReg r=s.getReg r := by
  unfold unpackedEnd
  rw [endKept _ r h,loopKept _ _ _ r h,resetKept _ r h,loopKept _ _ _ r h,initKept _ r h,MachineState.getReg_setPC]

theorem unpackedLen (s : MachineState) : (unpackedEnd s).getReg .x17=71680 := by
  have endValue (t : MachineState) : (endState true t).getReg .x17=71680 := by
    simp [endState,endOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12]
  exact endValue _

theorem unpackedPC (s : MachineState) : (unpackedEnd s).pc=loc 222 := by
  let t:=s.setPC (loc 413)
  have first:=firstCursors true t rfl
  have a:=allCursors true false 128 (by decide) _ first
  have b:=nextCursors true _ a
  have c:=allCursors true true 128 (by decide) _ b
  have e : (secondPhase true t).pc=loc 983:=endPC true _ c
  change (endState true (secondPhase true t)).pc=_
  simp [endState,endOps,execInstrBr,MachineState.setPC,e,loc,signExtend21]

end CommitGolfCandidate.Trunc.Wire
