import CommitGolfCandidate.TruncPhaseRun
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

def startIx (b : Bool) : Nat := if b then 413 else 142
def resetIx (b : Bool) : Nat := if b then 463 else 663
def endIx (b : Bool) : Nat := if b then 983 else 698
private theorem initCode (b : Bool) : Slice (im b) (startIx b) (initOps b) := by
  cases b <;> intro j hj <;> change j<15 at hj <;> interval_cases j <;> rfl
private theorem endCode (b : Bool) : Slice (im b) (endIx b) (endOps b) := by
  cases b <;> intro j hj
  · change j<5 at hj;interval_cases j <;> rfl
  · change j<8 at hj;interval_cases j <;> rfl

theorem initRun (b : Bool) (s : MachineState) (pc : s.pc=loc (startIx b)) :
    Runs (im b) s (init b s) 15 15 := by
  have h:=controlRun (im b) (startIx b) (initOps b) s pc (by cases b <;> decide) (initCode b)
    (by cases b <;> intro j <;> fin_cases j <;> rfl) (by cases b <;> intro j _ <;> fin_cases j <;> rfl)
  cases b <;> exact h

theorem resetRun (b : Bool) (s : MachineState) (pc : s.pc=loc (resetIx b)) : Runs (im b) s (reset s) 1 1 := by
  apply one (resetIx b) s _ (.ADDI .x28 .x0 128) (by cases b <;> decide) pc (by cases b <;> rfl) _ rfl
  rfl

theorem endRun (b : Bool) (s : MachineState) (pc : s.pc=loc (endIx b)) :
    Runs (im b) s (endState b s) (if b then 8 else 5) (if b then 8 else 5) := by
  have h:=controlRun (im b) (endIx b) (endOps b) s pc (by cases b <;> decide) (endCode b)
    (by cases b <;> intro j <;> fin_cases j <;> rfl)
    (by cases b <;> intro j hj <;> fin_cases j <;> first | rfl | contradiction)
  cases b <;> exact h

theorem initMem (b : Bool) (s : MachineState) : (init b s).mem=s.mem := by cases b <;> rfl
theorem endMem (b : Bool) (s : MachineState) : (endState b s).mem=s.mem := by cases b <;> rfl

private theorem initData (b : Bool) (s : MachineState) :
    (init b s).getReg .x18=(if b then 10871708192 else 10871640096) ∧
    (init b s).getReg .x19=(if b then 10871711776 else 10871640096) ∧ (init b s).getReg .x28=128 := by
  cases b <;> simp [init,initOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12]

private theorem initPC (b : Bool) (s : MachineState) (pc : s.pc=loc (startIx b)) :
    (init b s).pc=loc (rowPC b (!b)) := by
  cases b <;> simp [init,initOps,execInstrBr,MachineState.setPC,pc,loc,rowPC,startIx]

theorem firstCursors (b : Bool) (s : MachineState) (pc : s.pc=loc (startIx b)) : Cursors b (!b) 0 (init b s) := by
  obtain ⟨src,dst,remaining⟩:=initData b s
  have pos:=initPC b s pc
  cases b <;> exact ⟨src,dst,remaining,pos⟩

theorem resetPC (b : Bool) (s : MachineState) (f : Cursors b (!b) 128 s) : s.pc=loc (resetIx b) := by
  have h:=f.pc;simp only [ite_true,cores] at h
  cases b <;> exact h

theorem nextCursors (b : Bool) (s : MachineState) (f : Cursors b (!b) 128 s) : Cursors b b 0 (reset s) := by
  obtain ⟨x,y,k,pc⟩:=f
  cases b <;> refine ⟨x,y,rfl,?_⟩ <;> change s.pc+4=_ <;> rw [pc,cores] <;> rfl

theorem endPC (b : Bool) (s : MachineState) (f : Cursors b b 128 s) : s.pc=loc (endIx b) := by
  have h:=f.pc;simp only [ite_true,cores] at h
  cases b <;> exact h

end CommitGolfCandidate.Trunc.Wire
