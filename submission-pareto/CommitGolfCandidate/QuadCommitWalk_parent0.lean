import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_0 : walk 32 Artifact.commitCode (fun _ => parentWords) 94375 (List.range' 0 512) = some 96423 := by
  decide +kernel
theorem parent_block_512 : walk 32 Artifact.commitCode (fun _ => parentWords) 96423 (List.range' 512 512) = some 98471 := by
  decide +kernel
theorem parent_block_1024 : walk 32 Artifact.commitCode (fun _ => parentWords) 98471 (List.range' 1024 512) = some 100519 := by
  decide +kernel
theorem parent_block_1536 : walk 32 Artifact.commitCode (fun _ => parentWords) 100519 (List.range' 1536 512) = some 102567 := by
  decide +kernel
theorem parent_block_2048 : walk 32 Artifact.commitCode (fun _ => parentWords) 102567 (List.range' 2048 512) = some 104615 := by
  decide +kernel
theorem parent_block_2560 : walk 32 Artifact.commitCode (fun _ => parentWords) 104615 (List.range' 2560 512) = some 106663 := by
  decide +kernel
theorem parent_block_3072 : walk 32 Artifact.commitCode (fun _ => parentWords) 106663 (List.range' 3072 512) = some 108711 := by
  decide +kernel
theorem parent_block_3584 : walk 32 Artifact.commitCode (fun _ => parentWords) 108711 (List.range' 3584 512) = some 110759 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
