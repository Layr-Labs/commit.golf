import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_10752 : walk 32 Artifact.commitCode (fun _ => parentWords) 186546 (List.range' 10752 512) = some 188594 := by
  decide +kernel
theorem parent_block_11264 : walk 32 Artifact.commitCode (fun _ => parentWords) 188594 (List.range' 11264 512) = some 190642 := by
  decide +kernel
theorem parent_block_11776 : walk 32 Artifact.commitCode (fun _ => parentWords) 190642 (List.range' 11776 512) = some 192690 := by
  decide +kernel
theorem parent_block_12288 : walk 32 Artifact.commitCode (fun _ => parentWords) 192690 (List.range' 12288 512) = some 194738 := by
  decide +kernel
theorem parent_block_12800 : walk 32 Artifact.commitCode (fun _ => parentWords) 194738 (List.range' 12800 512) = some 196786 := by
  decide +kernel
theorem parent_block_13312 : walk 32 Artifact.commitCode (fun _ => parentWords) 196786 (List.range' 13312 512) = some 198834 := by
  decide +kernel
theorem parent_block_13824 : walk 32 Artifact.commitCode (fun _ => parentWords) 198834 (List.range' 13824 157) = some 199462 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
