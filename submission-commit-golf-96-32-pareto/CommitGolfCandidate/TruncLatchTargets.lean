import CommitGolfCandidate.TruncPhaseCode
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 300000

def branchOff (n : Nat) := BitVec.ofNat 13 (8192-4*(n+3))

theorem latchTarget (b f : Bool) :
    loc (rowPC b f+(sequence b f).length+2)+4+signExtend13 (branchOff (sequence b f).length)=loc (rowPC b f) ∧
    loc (rowPC b f+(sequence b f).length+2)+4+4=loc (rowPC b f)+BitVec.ofNat 64 (4*((sequence b f).length+4)) := by
  rw [cores];cases b <;> cases f <;> decide

end CommitGolfCandidate.Trunc.Wire
