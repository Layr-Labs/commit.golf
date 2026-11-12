import CommitGolfCandidate.LongParentSchedule

/-! N=2^24 leaves require 15 initial parents and 200 groups of 83886.
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
    branchPC := 1011392
    loopOffset := 1090512
    exitOffset := 1090168
    width := 83886 }

theorem group341_schedule_valid : group341Schedule.Valid := by
  constructor
  · decide
  · exact (long_parent_sequence_end 4760 83886).trans (by rfl)
  · decide
  · decide
  · decide

theorem group341_schedule_entry : group341Schedule.initialPlan.entry=4388 := rfl

theorem group341_schedule_parents (groups : Nat) : group341Schedule.parents groups=83886*groups+15 := by
  change 15+83886*groups=83886*groups+15
  omega

theorem group341_schedule_instructions (groups : Nat) :
    group341Schedule.instructions groups=251660*groups+49 := by
  change 49+251660*groups=251660*groups+49
  omega

theorem group341_schedule_cycles (groups : Nat) : group341Schedule.cycles groups=838862*groups+154 := by
  change 154+838862*groups=838862*groups+154
  omega

end CommitGolfCandidate
