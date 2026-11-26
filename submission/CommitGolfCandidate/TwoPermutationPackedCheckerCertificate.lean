import CommitGolfCandidate.TwoPermutationPackedCheckerFromRecord
import CommitGolfCandidate.TwoPermutationPackedRecordComposition
import CommitGolfCandidate.TwoPermutationPackedLeafComplete
import CommitGolfCandidate.TwoPermutationPackedLowerAdapter
import CommitGolfCandidate.TwoPermutationPackedLevel
import CommitGolfCandidate.K3T238Arm

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf RiscvZkvm.Rv64

theorem checker_from_phases (leaf : Oracle → Nat → Index → MachineState → RecordBlock)
    (step : Oracle → Nat → Index → Nat → MachineState → RecordBlock)
    (leafVerified : LeafBlockRefines leaf) (stepVerified : LowerStepRefines step) :
    QuartetCertificate.CheckerFacts PackedChecker.submission :=
  checker_facts_from_record (joinedRecord leaf step) (joined_record_refines leaf step leafVerified stepVerified)

/-- The lower-loop step: C's L21 arm for loop levels `0..4`, C3's T238 arm for `5..13`. -/
def lowerStep (oracle : Oracle) (ordinal : Nat) (index : Index) (level : Nat) (state : MachineState) : RecordBlock :=
  if level ≤ 4 then lowStep oracle ordinal index level state else t238Step oracle ordinal index level state

theorem lower_step_refines : LowerStepRefines lowerStep := by
  intro oracle ordinal index level state within room cursor
  unfold lowerStep
  by_cases low : level ≤ 4
  · rw [if_pos low]
    exact low_step_facts oracle ordinal index level state low room cursor
  · rw [if_neg low]
    exact t238_step_facts oracle ordinal index level state (by omega) within room cursor

theorem executable_checker_facts : QuartetCertificate.CheckerFacts PackedChecker.submission :=
  checker_from_phases RecordLeaf.block lowerStep RecordLeaf.actual_leaf_block lower_step_refines

end TwoPermutationPrototype.Packed.Checker
