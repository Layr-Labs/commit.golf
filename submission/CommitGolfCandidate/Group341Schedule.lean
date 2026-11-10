import CommitGolfCandidate.LongParentSchedule

/-! N=2^24 leaves require 15 initial parents and 3075 groups of 5456.
A short forward branch selects either a root-return or backward long jump. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def group341Schedule : LongParentSchedule :=
  { initialPlan := .stage 4388 1 4400 8108
      (.stage 4316 2 4340 260
        (.stage 4600 4 4648 8
          (.stage 4656 8 4752 8 (.done 4760))))
    start := 4760
    branchPC := 70232
    loopOffset := 2031672
    exitOffset := 2031328
    width := 5456 }

theorem group341_schedule_valid : group341Schedule.Valid := by
  constructor <;> decide

theorem group341_schedule_entry : group341Schedule.initialPlan.entry=4388 := rfl

theorem group341_schedule_parents (groups : Nat) : group341Schedule.parents groups=5456*groups+15 := by
  change 15+5456*groups=5456*groups+15
  omega

theorem group341_schedule_instructions (groups : Nat) :
    group341Schedule.instructions groups=16370*groups+49 := by
  change 49+16370*groups=16370*groups+49
  omega

theorem group341_schedule_cycles (groups : Nat) : group341Schedule.cycles groups=54562*groups+154 := by
  change 154+54562*groups=54562*groups+154
  omega

end CommitGolfCandidate
