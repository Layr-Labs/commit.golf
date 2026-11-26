import CommitGolfCandidate.TruncPreparePrefix
import CommitGolfCandidate.TruncSetupConstant
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

def enterState (s : MachineState) :=
  ((parentStartPrefix s 11).setReg .x17 (BitVec.ofNat 64 switchPtr)).setPC (loc 593)

private theorem enterCode : ((submission.image .commit).code[592]?).bind decodeInstruction=some (.base (.JAL .x0 816)) := by
  let old:=(CommitGolfCandidate.submission.image .commit).code
  have len : old.length=796 := rfl
  change (((((old.set 592 0x3300006f).set 691 _).set 692 _) ++ _)[592]?).bind decodeInstruction=_
  rw [List.getElem?_append_left (by simp only [List.length_set,len];decide),
      List.getElem?_set_ne (by decide),List.getElem?_set_ne (by decide),List.getElem?_set_self (by rw [len];decide)]
  rfl

private theorem leaveCode : ((submission.image .commit).code[801]?).bind decodeInstruction=some (.base (.JAL .x0 2096320)) := by
  rw [show (801:Nat)=796+5 by decide,suffixWord];rfl

private theorem startPC (s : MachineState) (pc : s.pc=6420) : (parentStartPrefix s 11).pc=loc 592 := by
  simp [parentStartPrefix,parentStartInstructions,execInstrBr,pc,loc,MachineState.setPC]

private theorem setupJump (p : MachineState) (pc : p.pc=loc 592) :
    Runs (submission.image .commit) p ((p.setReg .x17 (BitVec.ofNat 64 switchPtr)).setPC (loc 593)) 7 7 := by
  let m:=p.setPC (loc 796)
  let e:=(m.setReg .x17 (BitVec.ofNat 64 switchPtr)).setPC (loc 801)
  have j : Runs (submission.image .commit) p m 1 1 :=
    jumpAt _ p 592 796 816 (by decide) pc enterCode (by decide)
  have mid : Runs (submission.image .commit) m e 5 5 := constantRun m rfl
  have leave : Runs (submission.image .commit) e (e.setPC (loc 593)) 1 1 :=
    jumpAt _ e 801 593 2096320 (by decide) rfl leaveCode (by decide)
  exact chain (chain j mid) leave

attribute [local irreducible] parentStartPrefix Runs in
theorem enterRun (s : MachineState) (pc : s.pc=6420) : Runs (submission.image .commit) s (enterState s) 18 18 :=
  chain (prepare11 s pc) (setupJump _ (startPC s pc))

theorem entryMem (s : MachineState) : (enterState s).mem=s.mem := rfl

private theorem parent_start_prefix_register (state : MachineState) (reg : Reg)
    (n6 : reg ≠ .x6) (n21 : reg ≠ .x21) (n22 : reg ≠ .x22) (n24 : reg ≠ .x24) :
    (parentStartPrefix state 11).getReg reg = state.getReg reg := by
  simp only [parentStartPrefix, parentStartInstructions, List.take, List.foldl, execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n6),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n21),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n22),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n24)]

set_option maxRecDepth 20000 in
private theorem parent_start_prefix_pointers (state : MachineState) :
    (parentStartPrefix state 11).getReg .x21 = state.getReg .x23 + 18446744073709550080 ∧
    (parentStartPrefix state 11).getReg .x24 = 3072 ∧
    (parentStartPrefix state 11).getReg .x22 = state.getReg .x9 + 805304832 := by
  dsimp only [parentStartPrefix, parentStartInstructions, List.take, List.foldl, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

private theorem keepPrefix (s : MachineState) (r : Reg) (hr : Reg.x17≠r) :
    (enterState s).getReg r=(parentStartPrefix s 11).getReg r := by
  rw [enterState,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ hr]

theorem enterFrame (s : MachineState) (pc : s.pc=6420) (r9 : s.getReg .x9=BitVec.ofNat 64 heapBase)
    (r23 : s.getReg .x23=BitVec.ofNat 64 (heapBase+96*2^24)) (rt : s.getReg .x26=4294971392)
    (r5 : s.getReg .x5=0) (r11 : s.getReg .x11=96) (r13 : s.getReg .x13=0) :
    ParentFrame (2^24-1) (enterState s) := by
  have ptr:=parent_start_prefix_pointers s
  have kept (r : Reg) (n17 : .x17≠r) (n6 : r≠.x6) (n21 : r≠.x21) (n22 : r≠.x22) (n24 : r≠.x24) :=
    (keepPrefix s r n17).trans (parent_start_prefix_register s r n6 n21 n22 n24)
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩,rfl⟩
  · exact (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans r9
  · rw [keepPrefix _ _ (by decide),ptr.1,r23];decide
  · rw [keepPrefix _ _ (by decide),ptr.2.2,r9];decide
  · exact (keepPrefix _ _ (by decide)).trans ptr.2.1
  · simp only [enterState,MachineState.getReg_setPC,MachineState.getReg_setReg_eq] <;> rfl
  · exact (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans rt
  · exact (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans r5
  · exact (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans r11
  · exact (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans r13

end CommitGolfCandidate.Trunc
