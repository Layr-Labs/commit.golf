import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_0 : walk 32 Artifact.commitCode (fun _ => parentWords) 143538 (List.range' 0 512) = some 145586 := by
  decide +kernel
theorem parent_block_512 : walk 32 Artifact.commitCode (fun _ => parentWords) 145586 (List.range' 512 512) = some 147634 := by
  decide +kernel
theorem parent_block_1024 : walk 32 Artifact.commitCode (fun _ => parentWords) 147634 (List.range' 1024 512) = some 149682 := by
  decide +kernel
theorem parent_block_1536 : walk 32 Artifact.commitCode (fun _ => parentWords) 149682 (List.range' 1536 512) = some 151730 := by
  decide +kernel
theorem parent_block_2048 : walk 32 Artifact.commitCode (fun _ => parentWords) 151730 (List.range' 2048 512) = some 153778 := by
  decide +kernel
theorem parent_block_2560 : walk 32 Artifact.commitCode (fun _ => parentWords) 153778 (List.range' 2560 512) = some 155826 := by
  decide +kernel
theorem parent_block_3072 : walk 32 Artifact.commitCode (fun _ => parentWords) 155826 (List.range' 3072 512) = some 157874 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
