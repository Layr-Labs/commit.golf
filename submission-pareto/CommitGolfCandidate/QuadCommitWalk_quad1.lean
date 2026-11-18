import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem quad_block_1024 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 57500 (List.range' 1024 128) = some 59036 := by
  decide +kernel
theorem quad_block_1152 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 59036 (List.range' 1152 128) = some 60572 := by
  decide +kernel
theorem quad_block_1280 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 60572 (List.range' 1280 128) = some 62108 := by
  decide +kernel
theorem quad_block_1408 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 62108 (List.range' 1408 128) = some 63644 := by
  decide +kernel
theorem quad_block_1536 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 63644 (List.range' 1536 128) = some 65180 := by
  decide +kernel
theorem quad_block_1664 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 65180 (List.range' 1664 128) = some 66716 := by
  decide +kernel
theorem quad_block_1792 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 66716 (List.range' 1792 128) = some 68252 := by
  decide +kernel
theorem quad_block_1920 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 68252 (List.range' 1920 128) = some 69788 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
