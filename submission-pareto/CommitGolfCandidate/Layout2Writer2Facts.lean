import CommitGolfCandidate.Layout2Writer2Run
import CommitGolfCandidate.GroupOpenImage

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolfCandidate
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem phase2_rows (p : Nat) (hp : p<4) : Layout2Writer2.ImageAt openingImage p := by
  interval_cases p <;> decide +kernel

theorem layout2_writer2_facts (p : Nat) (hp : p<4) : Layout2Phase2.PhaseFacts openingImage p :=
  Layout2Writer2.phase_facts (phase2_rows p hp)

end TwoPermutationPrototype.GroupedOpening
