import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_3072 : walk 32 Artifact.commitCode leafWords 33892 (List.range' 3072 128) = some 35304 := by
  decide +kernel
theorem leaf_block_3200 : walk 32 Artifact.commitCode leafWords 35304 (List.range' 3200 128) = some 36715 := by
  decide +kernel
theorem leaf_block_3328 : walk 32 Artifact.commitCode leafWords 36715 (List.range' 3328 128) = some 38127 := by
  decide +kernel
theorem leaf_block_3456 : walk 32 Artifact.commitCode leafWords 38127 (List.range' 3456 128) = some 39538 := by
  decide +kernel
theorem leaf_block_3584 : walk 32 Artifact.commitCode leafWords 39538 (List.range' 3584 128) = some 40950 := by
  decide +kernel
theorem leaf_block_3712 : walk 32 Artifact.commitCode leafWords 40950 (List.range' 3712 128) = some 42361 := by
  decide +kernel
theorem leaf_block_3840 : walk 32 Artifact.commitCode leafWords 42361 (List.range' 3840 128) = some 43773 := by
  decide +kernel
theorem leaf_block_3968 : walk 32 Artifact.commitCode leafWords 43773 (List.range' 3968 128) = some 45185 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
