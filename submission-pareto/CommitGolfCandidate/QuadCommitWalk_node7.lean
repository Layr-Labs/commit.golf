import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 209403 (List.range' 0 420) = some 210663 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 210672 (List.range' 0 210) = some 211302 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 211311 (List.range' 0 42) = some 211437 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 211458 (List.range' 0 9) = some 211485 := by
  decide +kernel
theorem n14r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 211498 (List.range' 0 2) = some 211504 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
