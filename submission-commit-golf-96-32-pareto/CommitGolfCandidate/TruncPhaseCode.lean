import CommitGolfCandidate.TruncControlBlock
import CommitGolfCandidate.TruncPhaseFrame
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 300000

def ptrOps (b f : Bool) : List Instr :=
  [.ADDI .x18 .x18 (BitVec.ofNat 12 (if b then 4096-srcWidth b f else srcWidth b f)),
   .ADDI .x19 .x19 (BitVec.ofNat 12 (if b then 4096-dstWidth b f else dstWidth b f))]
def ptrPC (b f : Bool) := rowPC b f+(if b then 0 else (sequence b f).length)
def latchOps (b f : Bool) : List Instr :=
  [.ADDI .x28 .x28 4095,.BNE .x28 .x0 (BitVec.ofNat 13 (8192-4*((sequence b f).length+3)))]

theorem ptrCode (b f : Bool) : Slice (im b) (ptrPC b f) (ptrOps b f) := by
  intro j hj;change j<2 at hj
  simp only [ptrPC,cores]
  cases b <;> cases f <;> interval_cases j <;> rfl
theorem latchCode (b f : Bool) : Slice (im b) (rowPC b f+(sequence b f).length+2) (latchOps b f) := by
  intro j hj;change j<2 at hj
  simp only [latchOps,cores]
  cases b <;> cases f <;> interval_cases j <;> rfl

end CommitGolfCandidate.Trunc.Wire
