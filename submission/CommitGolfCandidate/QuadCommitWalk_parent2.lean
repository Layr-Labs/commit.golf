import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_8192 : walk 32 Artifact.commitCode (fun _ => parentWords) 127143 (List.range' 8192 512) = some 129191 := by
  decide +kernel
theorem parent_block_8704 : walk 32 Artifact.commitCode (fun _ => parentWords) 129191 (List.range' 8704 512) = some 131239 := by
  decide +kernel
theorem parent_block_9216 : walk 32 Artifact.commitCode (fun _ => parentWords) 131239 (List.range' 9216 512) = some 133287 := by
  decide +kernel
theorem parent_block_9728 : walk 32 Artifact.commitCode (fun _ => parentWords) 133287 (List.range' 9728 512) = some 135335 := by
  decide +kernel
theorem parent_block_10240 : walk 32 Artifact.commitCode (fun _ => parentWords) 135335 (List.range' 10240 512) = some 137383 := by
  decide +kernel
theorem parent_block_10752 : walk 32 Artifact.commitCode (fun _ => parentWords) 137383 (List.range' 10752 512) = some 139431 := by
  decide +kernel
theorem parent_block_11264 : walk 32 Artifact.commitCode (fun _ => parentWords) 139431 (List.range' 11264 512) = some 141479 := by
  decide +kernel
theorem parent_block_11776 : walk 32 Artifact.commitCode (fun _ => parentWords) 141479 (List.range' 11776 512) = some 143527 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
