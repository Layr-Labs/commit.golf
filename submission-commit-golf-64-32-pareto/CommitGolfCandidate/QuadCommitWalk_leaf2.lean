import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_2048 : walk 32 Artifact.commitCode leafWords 22609 (List.range' 2048 128) = some 24021 := by
  decide +kernel
theorem leaf_block_2176 : walk 32 Artifact.commitCode leafWords 24021 (List.range' 2176 128) = some 25433 := by
  decide +kernel
theorem leaf_block_2304 : walk 32 Artifact.commitCode leafWords 25433 (List.range' 2304 128) = some 26845 := by
  decide +kernel
theorem leaf_block_2432 : walk 32 Artifact.commitCode leafWords 26845 (List.range' 2432 128) = some 28257 := by
  decide +kernel
theorem leaf_block_2560 : walk 32 Artifact.commitCode leafWords 28257 (List.range' 2560 128) = some 29669 := by
  decide +kernel
theorem leaf_block_2688 : walk 32 Artifact.commitCode leafWords 29669 (List.range' 2688 128) = some 31081 := by
  decide +kernel
theorem leaf_block_2816 : walk 32 Artifact.commitCode leafWords 31081 (List.range' 2816 128) = some 32492 := by
  decide +kernel
theorem leaf_block_2944 : walk 32 Artifact.commitCode leafWords 32492 (List.range' 2944 128) = some 33904 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
