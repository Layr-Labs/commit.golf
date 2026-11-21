import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem qthree_block_4096 : walk 32 Artifact.commitCode (fun _ => quadWords) 155826 (List.range' 4096 512) = some 157362 := by
  decide +kernel
theorem qthree_block_4608 : walk 32 Artifact.commitCode (fun _ => quadWords) 157362 (List.range' 4608 512) = some 158898 := by
  decide +kernel
theorem qthree_block_5120 : walk 32 Artifact.commitCode (fun _ => quadWords) 158898 (List.range' 5120 512) = some 160434 := by
  decide +kernel
theorem qthree_block_5632 : walk 32 Artifact.commitCode (fun _ => quadWords) 160434 (List.range' 5632 512) = some 161970 := by
  decide +kernel
theorem qthree_block_6144 : walk 32 Artifact.commitCode (fun _ => quadWords) 161970 (List.range' 6144 512) = some 163506 := by
  decide +kernel
theorem qthree_block_6656 : walk 32 Artifact.commitCode (fun _ => quadWords) 163506 (List.range' 6656 512) = some 165042 := by
  decide +kernel
theorem qthree_block_7168 : walk 32 Artifact.commitCode (fun _ => quadWords) 165042 (List.range' 7168 512) = some 166578 := by
  decide +kernel
theorem qthree_block_7680 : walk 32 Artifact.commitCode (fun _ => quadWords) 166578 (List.range' 7680 512) = some 168114 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
