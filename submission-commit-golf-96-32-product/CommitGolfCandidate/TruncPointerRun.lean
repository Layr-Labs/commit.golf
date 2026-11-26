import CommitGolfCandidate.TruncPhaseCode
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 300000

theorem runsTo {im : Image} {s t u : MachineState} {n c : Nat} (run : Runs im s t n c) (eqn : t=u) :
    Runs im s u n c := eqn ▸ run

theorem pointerRun (b f : Bool) (s : MachineState) (pc : s.pc=loc (ptrPC b f)) :
    Runs (im b) s (pointers b f s) 2 2 := by
  have result := controlRun (im b) (ptrPC b f) (ptrOps b f) s pc
    (by change ptrPC b f+2≤2048;unfold ptrPC;rw [cores];cases b <;> cases f <;> decide)
    (ptrCode b f) (by intro k;fin_cases k <;> rfl)
    (by intro k hk;fin_cases k <;> rfl)
  have eqn : (ptrOps b f).foldl execInstrBr s=pointers b f s := by
    cases b <;> cases f <;> simp [ptrOps,pointers,srcWidth,dstWidth,short,wide,execInstrBr,
      MachineState.setPC,MachineState.setReg,MachineState.getReg,signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  exact runsTo result eqn

end CommitGolfCandidate.Trunc.Wire
