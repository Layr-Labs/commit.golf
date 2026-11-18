import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem quad_block_4096 : walk 32 Artifact.commitCode (fun _ => quadWords) 57500 (List.range' 4096 512) = some 59036 := by
  decide +kernel
theorem quad_block_4608 : walk 32 Artifact.commitCode (fun _ => quadWords) 59036 (List.range' 4608 512) = some 60572 := by
  decide +kernel
theorem quad_block_5120 : walk 32 Artifact.commitCode (fun _ => quadWords) 60572 (List.range' 5120 512) = some 62108 := by
  decide +kernel
theorem quad_block_5632 : walk 32 Artifact.commitCode (fun _ => quadWords) 62108 (List.range' 5632 512) = some 63644 := by
  decide +kernel
theorem quad_block_6144 : walk 32 Artifact.commitCode (fun _ => quadWords) 63644 (List.range' 6144 512) = some 65180 := by
  decide +kernel
theorem quad_block_6656 : walk 32 Artifact.commitCode (fun _ => quadWords) 65180 (List.range' 6656 512) = some 66716 := by
  decide +kernel
theorem quad_block_7168 : walk 32 Artifact.commitCode (fun _ => quadWords) 66716 (List.range' 7168 512) = some 68252 := by
  decide +kernel
theorem quad_block_7680 : walk 32 Artifact.commitCode (fun _ => quadWords) 68252 (List.range' 7680 512) = some 69788 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
