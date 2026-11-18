import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem quad_block_0 : walk 32 Artifact.commitCode (fun _ => quadWords) 45212 (List.range' 0 512) = some 46748 := by
  decide +kernel
theorem quad_block_512 : walk 32 Artifact.commitCode (fun _ => quadWords) 46748 (List.range' 512 512) = some 48284 := by
  decide +kernel
theorem quad_block_1024 : walk 32 Artifact.commitCode (fun _ => quadWords) 48284 (List.range' 1024 512) = some 49820 := by
  decide +kernel
theorem quad_block_1536 : walk 32 Artifact.commitCode (fun _ => quadWords) 49820 (List.range' 1536 512) = some 51356 := by
  decide +kernel
theorem quad_block_2048 : walk 32 Artifact.commitCode (fun _ => quadWords) 51356 (List.range' 2048 512) = some 52892 := by
  decide +kernel
theorem quad_block_2560 : walk 32 Artifact.commitCode (fun _ => quadWords) 52892 (List.range' 2560 512) = some 54428 := by
  decide +kernel
theorem quad_block_3072 : walk 32 Artifact.commitCode (fun _ => quadWords) 54428 (List.range' 3072 512) = some 55964 := by
  decide +kernel
theorem quad_block_3584 : walk 32 Artifact.commitCode (fun _ => quadWords) 55964 (List.range' 3584 512) = some 57500 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
