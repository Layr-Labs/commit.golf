import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_10752 : walk 32 Artifact.commitCode (fun _ => parentWords) 235709 (List.range' 10752 512) = some 237757 := by
  decide +kernel
theorem parent_block_11264 : walk 32 Artifact.commitCode (fun _ => parentWords) 237757 (List.range' 11264 512) = some 239805 := by
  decide +kernel
theorem parent_block_11776 : walk 32 Artifact.commitCode (fun _ => parentWords) 239805 (List.range' 11776 512) = some 241853 := by
  decide +kernel
theorem parent_block_12288 : walk 32 Artifact.commitCode (fun _ => parentWords) 241853 (List.range' 12288 512) = some 243901 := by
  decide +kernel
theorem parent_block_12800 : walk 32 Artifact.commitCode (fun _ => parentWords) 243901 (List.range' 12800 512) = some 245949 := by
  decide +kernel
theorem parent_block_13312 : walk 32 Artifact.commitCode (fun _ => parentWords) 245949 (List.range' 13312 485) = some 247889 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
