import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_3072 : walk 32 Artifact.commitCode leafWords 33903 (List.range' 3072 128) = some 35315 := by
  decide +kernel
theorem leaf_block_3200 : walk 32 Artifact.commitCode leafWords 35315 (List.range' 3200 128) = some 36726 := by
  decide +kernel
theorem leaf_block_3328 : walk 32 Artifact.commitCode leafWords 36726 (List.range' 3328 128) = some 38138 := by
  decide +kernel
theorem leaf_block_3456 : walk 32 Artifact.commitCode leafWords 38138 (List.range' 3456 128) = some 39550 := by
  decide +kernel
theorem leaf_block_3584 : walk 32 Artifact.commitCode leafWords 39550 (List.range' 3584 128) = some 40962 := by
  decide +kernel
theorem leaf_block_3712 : walk 32 Artifact.commitCode leafWords 40962 (List.range' 3712 128) = some 42374 := by
  decide +kernel
theorem leaf_block_3840 : walk 32 Artifact.commitCode leafWords 42374 (List.range' 3840 128) = some 43786 := by
  decide +kernel
theorem leaf_block_3968 : walk 32 Artifact.commitCode leafWords 43786 (List.range' 3968 128) = some 45199 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
