import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_1024 : walk 32 Artifact.commitCode leafWords 11313 (List.range' 1024 128) = some 12725 := by
  decide +kernel
theorem leaf_block_1152 : walk 32 Artifact.commitCode leafWords 12725 (List.range' 1152 128) = some 14137 := by
  decide +kernel
theorem leaf_block_1280 : walk 32 Artifact.commitCode leafWords 14137 (List.range' 1280 128) = some 15549 := by
  decide +kernel
theorem leaf_block_1408 : walk 32 Artifact.commitCode leafWords 15549 (List.range' 1408 128) = some 16961 := by
  decide +kernel
theorem leaf_block_1536 : walk 32 Artifact.commitCode leafWords 16961 (List.range' 1536 128) = some 18372 := by
  decide +kernel
theorem leaf_block_1664 : walk 32 Artifact.commitCode leafWords 18372 (List.range' 1664 128) = some 19784 := by
  decide +kernel
theorem leaf_block_1792 : walk 32 Artifact.commitCode leafWords 19784 (List.range' 1792 128) = some 21196 := by
  decide +kernel
theorem leaf_block_1920 : walk 32 Artifact.commitCode leafWords 21196 (List.range' 1920 128) = some 22608 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
