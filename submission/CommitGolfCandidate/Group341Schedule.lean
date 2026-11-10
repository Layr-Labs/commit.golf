import CommitGolfCandidate.ParentGroupSchedule

/-! N=2^24 leaves require 15 initial parents and 49200 groups of 341.
The backward branch spans 4092 bytes, within the signed 13-bit encoding. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def group341Schedule : ParentSchedule :=
  { initialPlan := .stage 4388 1 4400 8108
      (.stage 4316 2 4340 260
        (.stage 4600 4 4648 8
          (.stage 4656 8 4752 8 (.done 4760))))
    start := 4760
    branchPC := 8852
    branchOffset := 4100
    exitOffset := 2092708
    width := 341 }

theorem group341_schedule_valid : group341Schedule.Valid := by
  constructor <;> decide

theorem group341_schedule_entry : group341Schedule.initialPlan.entry=4388 := rfl

theorem group341_schedule_parents (groups : Nat) : group341Schedule.parents groups=341*groups+15 := by
  change 15+341*groups=341*groups+15
  omega

theorem group341_schedule_instructions (groups : Nat) :
    group341Schedule.instructions groups=1024*groups+50 := by
  change 49+1024*groups+1=1024*groups+50
  omega

theorem group341_schedule_cycles (groups : Nat) : group341Schedule.cycles groups=3411*groups+155 := by
  change 154+3411*groups+1=3411*groups+155
  omega

end CommitGolfCandidate
