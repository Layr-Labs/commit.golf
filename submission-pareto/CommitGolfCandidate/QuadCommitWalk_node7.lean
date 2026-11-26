import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 209403 (List.range' 0 420) = some 210663 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 210672 (List.range' 0 210) = some 211302 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 211311 (List.range' 0 105) = some 211626 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 211639 (List.range' 0 53) = some 211798 := by
  decide +kernel
theorem n14r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 211811 (List.range' 0 27) = some 211892 := by
  decide +kernel
theorem n15r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 211905 (List.range' 0 14) = some 211947 := by
  decide +kernel
theorem n16r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 211956 (List.range' 0 7) = some 211977 := by
  decide +kernel
theorem n17r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 211990 (List.range' 0 4) = some 212002 := by
  decide +kernel
theorem n18r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 212011 (List.range' 0 2) = some 212017 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
