import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_1024 : walk 32 Artifact.commitCode leafWords 11314 (List.range' 1024 128) = some 12726 := by
  decide +kernel
theorem leaf_block_1152 : walk 32 Artifact.commitCode leafWords 12726 (List.range' 1152 128) = some 14138 := by
  decide +kernel
theorem leaf_block_1280 : walk 32 Artifact.commitCode leafWords 14138 (List.range' 1280 128) = some 15550 := by
  decide +kernel
theorem leaf_block_1408 : walk 32 Artifact.commitCode leafWords 15550 (List.range' 1408 128) = some 16961 := by
  decide +kernel
theorem leaf_block_1536 : walk 32 Artifact.commitCode leafWords 16961 (List.range' 1536 128) = some 18373 := by
  decide +kernel
theorem leaf_block_1664 : walk 32 Artifact.commitCode leafWords 18373 (List.range' 1664 128) = some 19785 := by
  decide +kernel
theorem leaf_block_1792 : walk 32 Artifact.commitCode leafWords 19785 (List.range' 1792 128) = some 21197 := by
  decide +kernel
theorem leaf_block_1920 : walk 32 Artifact.commitCode leafWords 21197 (List.range' 1920 128) = some 22609 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
