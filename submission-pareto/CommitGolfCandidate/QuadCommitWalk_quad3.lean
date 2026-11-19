import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem quad_block_3072 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 82076 (List.range' 3072 128) = some 83612 := by
  decide +kernel
theorem quad_block_3200 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 83612 (List.range' 3200 128) = some 85148 := by
  decide +kernel
theorem quad_block_3328 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 85148 (List.range' 3328 128) = some 86684 := by
  decide +kernel
theorem quad_block_3456 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 86684 (List.range' 3456 128) = some 88220 := by
  decide +kernel
theorem quad_block_3584 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 88220 (List.range' 3584 128) = some 89756 := by
  decide +kernel
theorem quad_block_3712 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 89756 (List.range' 3712 128) = some 91292 := by
  decide +kernel
theorem quad_block_3840 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 91292 (List.range' 3840 128) = some 92828 := by
  decide +kernel
theorem quad_block_3968 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 92828 (List.range' 3968 128) = some 94364 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
