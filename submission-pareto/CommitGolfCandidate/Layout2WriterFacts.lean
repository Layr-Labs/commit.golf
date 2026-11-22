import CommitGolfCandidate.Layout2WriterRun
import CommitGolfCandidate.GroupOpenImage
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolfCandidate CommitGolfCandidate.Layout2Phase
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem phase_rows (p : Nat) (small : p<4) : Layout2Writer.BodyAt openingImage p := by
  interval_cases p <;> decide +kernel

/-- The four concrete phase bodies of the V1 opener, verified against the shared interface. -/
theorem layout2_writer_facts (p : Nat) (small : p<4) : PhaseFacts openingImage p :=
  Layout2Writer.phase_facts (phase_rows p small)

end TwoPermutationPrototype.GroupedOpening
