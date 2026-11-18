import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem quad_block_8192 : walk 32 Artifact.commitCode (fun _ => quadWords) 69788 (List.range' 8192 512) = some 71324 := by
  decide +kernel
theorem quad_block_8704 : walk 32 Artifact.commitCode (fun _ => quadWords) 71324 (List.range' 8704 512) = some 72860 := by
  decide +kernel
theorem quad_block_9216 : walk 32 Artifact.commitCode (fun _ => quadWords) 72860 (List.range' 9216 512) = some 74396 := by
  decide +kernel
theorem quad_block_9728 : walk 32 Artifact.commitCode (fun _ => quadWords) 74396 (List.range' 9728 512) = some 75932 := by
  decide +kernel
theorem quad_block_10240 : walk 32 Artifact.commitCode (fun _ => quadWords) 75932 (List.range' 10240 512) = some 77468 := by
  decide +kernel
theorem quad_block_10752 : walk 32 Artifact.commitCode (fun _ => quadWords) 77468 (List.range' 10752 512) = some 79004 := by
  decide +kernel
theorem quad_block_11264 : walk 32 Artifact.commitCode (fun _ => quadWords) 79004 (List.range' 11264 512) = some 80540 := by
  decide +kernel
theorem quad_block_11776 : walk 32 Artifact.commitCode (fun _ => quadWords) 80540 (List.range' 11776 512) = some 82076 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
