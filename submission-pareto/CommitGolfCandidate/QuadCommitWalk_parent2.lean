import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_7168 : walk 32 Artifact.commitCode (fun _ => parentWords) 221373 (List.range' 7168 512) = some 223421 := by
  decide +kernel
theorem parent_block_7680 : walk 32 Artifact.commitCode (fun _ => parentWords) 223421 (List.range' 7680 512) = some 225469 := by
  decide +kernel
theorem parent_block_8192 : walk 32 Artifact.commitCode (fun _ => parentWords) 225469 (List.range' 8192 512) = some 227517 := by
  decide +kernel
theorem parent_block_8704 : walk 32 Artifact.commitCode (fun _ => parentWords) 227517 (List.range' 8704 512) = some 229565 := by
  decide +kernel
theorem parent_block_9216 : walk 32 Artifact.commitCode (fun _ => parentWords) 229565 (List.range' 9216 512) = some 231613 := by
  decide +kernel
theorem parent_block_9728 : walk 32 Artifact.commitCode (fun _ => parentWords) 231613 (List.range' 9728 512) = some 233661 := by
  decide +kernel
theorem parent_block_10240 : walk 32 Artifact.commitCode (fun _ => parentWords) 233661 (List.range' 10240 512) = some 235709 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
