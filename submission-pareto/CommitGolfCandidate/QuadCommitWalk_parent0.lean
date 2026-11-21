import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_0 : walk 32 Artifact.commitCode (fun _ => parentWords) 192701 (List.range' 0 512) = some 194749 := by
  decide +kernel
theorem parent_block_512 : walk 32 Artifact.commitCode (fun _ => parentWords) 194749 (List.range' 512 512) = some 196797 := by
  decide +kernel
theorem parent_block_1024 : walk 32 Artifact.commitCode (fun _ => parentWords) 196797 (List.range' 1024 512) = some 198845 := by
  decide +kernel
theorem parent_block_1536 : walk 32 Artifact.commitCode (fun _ => parentWords) 198845 (List.range' 1536 512) = some 200893 := by
  decide +kernel
theorem parent_block_2048 : walk 32 Artifact.commitCode (fun _ => parentWords) 200893 (List.range' 2048 512) = some 202941 := by
  decide +kernel
theorem parent_block_2560 : walk 32 Artifact.commitCode (fun _ => parentWords) 202941 (List.range' 2560 512) = some 204989 := by
  decide +kernel
theorem parent_block_3072 : walk 32 Artifact.commitCode (fun _ => parentWords) 204989 (List.range' 3072 512) = some 207037 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
