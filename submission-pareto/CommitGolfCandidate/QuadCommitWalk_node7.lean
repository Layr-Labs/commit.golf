import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n14r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 185521 (List.range' 0 164) = some 186013 := by
  decide +kernel
theorem n15r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 186022 (List.range' 0 82) = some 186268 := by
  decide +kernel
theorem n16r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 186277 (List.range' 0 41) = some 186400 := by
  decide +kernel
theorem n17r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 186413 (List.range' 0 21) = some 186476 := by
  decide +kernel
theorem n18r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 186489 (List.range' 0 11) = some 186522 := by
  decide +kernel
theorem n19r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 186535 (List.range' 0 6) = some 186553 := by
  decide +kernel
theorem n20r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 186562 (List.range' 0 3) = some 186571 := by
  decide +kernel
theorem n21r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 186584 (List.range' 0 2) = some 186590 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
