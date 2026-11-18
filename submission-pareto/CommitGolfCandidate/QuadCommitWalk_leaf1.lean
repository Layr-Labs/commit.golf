import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_1024 : walk 32 Artifact.commitCode leafWords 11310 (List.range' 1024 128) = some 12722 := by
  decide +kernel
theorem leaf_block_1152 : walk 32 Artifact.commitCode leafWords 12722 (List.range' 1152 128) = some 14133 := by
  decide +kernel
theorem leaf_block_1280 : walk 32 Artifact.commitCode leafWords 14133 (List.range' 1280 128) = some 15545 := by
  decide +kernel
theorem leaf_block_1408 : walk 32 Artifact.commitCode leafWords 15545 (List.range' 1408 128) = some 16955 := by
  decide +kernel
theorem leaf_block_1536 : walk 32 Artifact.commitCode leafWords 16955 (List.range' 1536 128) = some 18367 := by
  decide +kernel
theorem leaf_block_1664 : walk 32 Artifact.commitCode leafWords 18367 (List.range' 1664 128) = some 19778 := by
  decide +kernel
theorem leaf_block_1792 : walk 32 Artifact.commitCode leafWords 19778 (List.range' 1792 128) = some 21190 := by
  decide +kernel
theorem leaf_block_1920 : walk 32 Artifact.commitCode leafWords 21190 (List.range' 1920 128) = some 22601 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
