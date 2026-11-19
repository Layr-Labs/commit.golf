import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_3072 : walk 32 Artifact.commitCode leafWords 33904 (List.range' 3072 128) = some 35316 := by
  decide +kernel
theorem leaf_block_3200 : walk 32 Artifact.commitCode leafWords 35316 (List.range' 3200 128) = some 36728 := by
  decide +kernel
theorem leaf_block_3328 : walk 32 Artifact.commitCode leafWords 36728 (List.range' 3328 128) = some 38140 := by
  decide +kernel
theorem leaf_block_3456 : walk 32 Artifact.commitCode leafWords 38140 (List.range' 3456 128) = some 39552 := by
  decide +kernel
theorem leaf_block_3584 : walk 32 Artifact.commitCode leafWords 39552 (List.range' 3584 128) = some 40964 := by
  decide +kernel
theorem leaf_block_3712 : walk 32 Artifact.commitCode leafWords 40964 (List.range' 3712 128) = some 42376 := by
  decide +kernel
theorem leaf_block_3840 : walk 32 Artifact.commitCode leafWords 42376 (List.range' 3840 128) = some 43788 := by
  decide +kernel
theorem leaf_block_3968 : walk 32 Artifact.commitCode leafWords 43788 (List.range' 3968 128) = some 45201 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
