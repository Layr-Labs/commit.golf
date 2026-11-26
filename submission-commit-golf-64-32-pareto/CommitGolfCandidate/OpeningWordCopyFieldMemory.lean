import CommitGolfCandidate.OpeningWordCopyMemory
import CommitGolfCandidate.ProjectedHalfwordMemory

namespace CommitGolfCandidate.OpeningWordCopy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 800000

theorem halfMemory_congr (count : Nat) (left right : MachineState) (source target : Word)
    (same : left.mem=right.mem) :
    (halfMemory count left source target).mem=(halfMemory count right source target).mem := by
  induction count generalizing left right source target with
  | zero => exact same
  | succ count ih =>
    apply ih
    simp only [MachineState.setHalfword,MachineState.setMem,MachineState.getHalfword,MachineState.getMem,same]

theorem halfMemory_add (a b : Nat) (state : MachineState) (source target : Word) :
    halfMemory (a+b) state source target =
      halfMemory b (halfMemory a state source target)
        (source+BitVec.ofNat 64 (2*a)) (target+BitVec.ofNat 64 (2*a)) := by
  induction a generalizing state source target with
  | zero => simp [halfMemory]
  | succ a ih =>
    rw [Nat.succ_add,halfMemory,ih,halfMemory]
    have shift (base : Word) : base+2+BitVec.ofNat 64 (2*a) = base+BitVec.ofNat 64 (2*(a+1)) := by
      rw [BitVec.add_assoc,show (2:Word)=BitVec.ofNat 64 2 by rfl,←BitVec.ofNat_add]
      congr 2
      omega
    rw [shift,shift]

theorem halfMemory_projected (count : Nat) (state : MachineState) (source target : Word) :
    halfMemory count state source target =
      ProjectedHalfword.copyLoopMemory false count state source target := by
  induction count generalizing state source target with
  | zero => rfl
  | succ count ih =>
    change halfMemory count _ (source+2) (target+2) =
      ProjectedHalfword.copyLoopMemory false count _ (source+2) (target+2)
    exact ih _ _ _

end CommitGolfCandidate.OpeningWordCopy
