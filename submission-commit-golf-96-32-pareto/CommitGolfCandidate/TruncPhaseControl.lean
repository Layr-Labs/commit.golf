import CommitGolfCandidate.TruncLatchTargets
import CommitGolfCandidate.TruncLatchState
import CommitGolfCandidate.TruncPointerRun
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 300000

theorem latchRun (b f : Bool) (s : MachineState)
    (pc : s.pc=loc (rowPC b f+(sequence b f).length+2)) :
    Runs (im b) s ((s.setReg .x28 (s.getReg .x28-1)).setPC
      (if s.getReg .x28-1=0 then loc (rowPC b f)+BitVec.ofNat 64 (4*((sequence b f).length+4)) else loc (rowPC b f))) 2 2 := by
  have result:=controlRun (im b) _ (latchOps b f) s pc
    (by change rowPC b f+(sequence b f).length+2+2≤2048;rw [cores];cases b <;> cases f <;> decide)
    (latchCode b f) (by intro k;fin_cases k <;> rfl)
    (by intro k hk
        have small : k.val+1<2:=hk
        have ix : k.val=0:=by omega
        have e : k=⟨0,by change 0<2;decide⟩:=Fin.ext ix
        subst k;rfl)
  have be : (latchOps b f).foldl execInstrBr s=
      (s.setReg .x28 (s.getReg .x28-1)).setPC
      (if s.getReg .x28-1=0 then loc (rowPC b f)+BitVec.ofNat 64 (4*((sequence b f).length+4)) else loc (rowPC b f)) := by
    have dest:=latchTarget b f
    exact latchState s (branchOff (sequence b f).length) _ _ (by rw [pc];exact dest.1) (by rw [pc];exact dest.2)
  exact runsTo result be

end CommitGolfCandidate.Trunc.Wire
