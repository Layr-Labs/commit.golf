import CommitGolfCandidate.TruncWireControl
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

def firstPhase (b : Bool) (s : MachineState) :=
  (regStep b (!b) (loc (rowPC b (!b))))^[128] (init b s)
def secondPhase (b : Bool) (s : MachineState) :=
  (regStep b b (loc (rowPC b b)))^[128] (reset (firstPhase b s))

theorem phases (b : Bool) (s : MachineState) (pc : s.pc=loc (startIx b)) :
    Runs (im b) s (endState b (secondPhase b s)) (if b then 70936 else 69141) (if b then 70936 else 69141) ∧
      Frame b s (endState b (secondPhase b s)) (if b then 0 else 68096) := by
  have a:=initRun b s pc
  have c:=firstCursors b s pc
  have start : Frame b s (init b s) (destStart b (!b) (cursor b 0)) := by
    have h:=frameMem (initialFrame b s) (initMem b s);cases b <;> exact h
  have run1:=phaseLoop b (!b) 128 0 (by decide) _ c
  obtain ⟨f,bytes1⟩:=allBytes b (!b) 128 (by decide) s _ c start
  have mid:=resetRun b (firstPhase b s) (resetPC b _ f)
  have c2:=nextCursors b _ f
  have start2 : Frame b s (reset (firstPhase b s)) (destStart b b (cursor b 0)) := by
    have h:=frameMem (z:=reset (firstPhase b s)) bytes1 (by rfl)
    cases b <;> exact h
  have run2:=phaseLoop b b 128 0 (by decide) _ c2
  obtain ⟨g,bytes2⟩:=allBytes b b 128 (by decide) s _ c2 start2
  have endR:=endRun b (secondPhase b s) (endPC b _ g)
  have run:=chain (chain (chain (chain a run1) mid) run2) endR
  have data:=frameMem bytes2 (endMem b (secondPhase b s))
  constructor
  · simp only [cores] at run;cases b <;> exact run
  · cases b <;> exact data

end CommitGolfCandidate.Trunc.Wire
