import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem quad_block_0 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 45212 (List.range' 0 128) = some 46748 := by
  decide +kernel
theorem quad_block_128 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 46748 (List.range' 128 128) = some 48284 := by
  decide +kernel
theorem quad_block_256 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 48284 (List.range' 256 128) = some 49820 := by
  decide +kernel
theorem quad_block_384 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 49820 (List.range' 384 128) = some 51356 := by
  decide +kernel
theorem quad_block_512 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 51356 (List.range' 512 128) = some 52892 := by
  decide +kernel
theorem quad_block_640 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 52892 (List.range' 640 128) = some 54428 := by
  decide +kernel
theorem quad_block_768 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 54428 (List.range' 768 128) = some 55964 := by
  decide +kernel
theorem quad_block_896 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 55964 (List.range' 896 128) = some 57500 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
