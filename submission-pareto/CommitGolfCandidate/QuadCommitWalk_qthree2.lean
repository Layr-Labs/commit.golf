import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem qthree_block_8192 : walk 32 Artifact.commitCode (fun _ => quadWords) 168114 (List.range' 8192 512) = some 169650 := by
  decide +kernel
theorem qthree_block_8704 : walk 32 Artifact.commitCode (fun _ => quadWords) 169650 (List.range' 8704 512) = some 171186 := by
  decide +kernel
theorem qthree_block_9216 : walk 32 Artifact.commitCode (fun _ => quadWords) 171186 (List.range' 9216 512) = some 172722 := by
  decide +kernel
theorem qthree_block_9728 : walk 32 Artifact.commitCode (fun _ => quadWords) 172722 (List.range' 9728 512) = some 174258 := by
  decide +kernel
theorem qthree_block_10240 : walk 32 Artifact.commitCode (fun _ => quadWords) 174258 (List.range' 10240 512) = some 175794 := by
  decide +kernel
theorem qthree_block_10752 : walk 32 Artifact.commitCode (fun _ => quadWords) 175794 (List.range' 10752 512) = some 177330 := by
  decide +kernel
theorem qthree_block_11264 : walk 32 Artifact.commitCode (fun _ => quadWords) 177330 (List.range' 11264 512) = some 178866 := by
  decide +kernel
theorem qthree_block_11776 : walk 32 Artifact.commitCode (fun _ => quadWords) 178866 (List.range' 11776 512) = some 180402 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
