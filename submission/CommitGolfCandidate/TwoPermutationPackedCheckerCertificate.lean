import CommitGolfCandidate.TwoPermutationPackedCheckerFromRecord
import CommitGolfCandidate.TwoPermutationPackedRecordComposition
import CommitGolfCandidate.TwoPermutationPackedLeafComplete
import CommitGolfCandidate.TwoPermutationPackedLowerAdapter
import CommitGolfCandidate.TwoPermutationPackedLevel
import CommitGolfCandidate.K3T238Arm

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf RiscvZkvm.Rv64

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


/-- Decoder-side interface for the delivered checker. Only the concrete table witness
changes when the opening format changes. -/
theorem executable_converted_observation (τ : CommitGolfCandidate.Layout2.Tables)
    (wf : CommitGolfCandidate.Layout2.WellFormed τ)
    (physical : ∀ k, k<85440 → GroupedOpening.pget K1Artifact.checkData k=CommitGolfCandidate.Layout2.tableByte τ k)
    (oracle : Oracle) (input : CheckInput) :
    CheckerObservationFacts oracle (CommitGolfCandidate.Layout2.converted τ (CommitGolfCandidate.Layout2.Quartet.prepared input))
      (TwoPermutationPrototype.Checker.checkObservation K1Artifact.submission oracle input) :=
  converted_observation τ wf physical (joinedRecord RecordLeaf.block lowerStep)
    (joined_record_refines RecordLeaf.block lowerStep RecordLeaf.actual_leaf_block lower_step_refines)
    checker_cap_facts oracle input

theorem binding_of_decoder (τ : CommitGolfCandidate.Layout2.Tables) (wf : CommitGolfCandidate.Layout2.WellFormed τ)
    (physical : ∀ k, k<85440 → GroupedOpening.pget K1Artifact.checkData k=CommitGolfCandidate.Layout2.tableByte τ k) :
    K1Artifact.submission.scheme.Binding := by
  apply TwoPermutationPrototype.Quartet.quartet_scheme_binding _ TwoPermutationPrototype.Sampling.k1_peer_leaf_layout_sharp
  intro oracle input
  dsimp only
  intro accepted
  have checked:=executable_converted_observation τ wf physical oracle input
  have count:=checked.queries
  have card:=TwoPermutationPrototype.Checker.checker_positions_bound input
  change _ ≤ 26*input.positions.card at count
  exact ⟨by omega,checked.paths accepted⟩

end TwoPermutationPrototype.Packed.Checker
