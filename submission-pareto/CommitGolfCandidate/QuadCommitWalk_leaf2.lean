import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_2048 : walk 32 Artifact.commitCode leafWords 22608 (List.range' 2048 128) = some 24020 := by
  decide +kernel
theorem leaf_block_2176 : walk 32 Artifact.commitCode leafWords 24020 (List.range' 2176 128) = some 25432 := by
  decide +kernel
theorem leaf_block_2304 : walk 32 Artifact.commitCode leafWords 25432 (List.range' 2304 128) = some 26844 := by
  decide +kernel
theorem leaf_block_2432 : walk 32 Artifact.commitCode leafWords 26844 (List.range' 2432 128) = some 28255 := by
  decide +kernel
theorem leaf_block_2560 : walk 32 Artifact.commitCode leafWords 28255 (List.range' 2560 128) = some 29667 := by
  decide +kernel
theorem leaf_block_2688 : walk 32 Artifact.commitCode leafWords 29667 (List.range' 2688 128) = some 31079 := by
  decide +kernel
theorem leaf_block_2816 : walk 32 Artifact.commitCode leafWords 31079 (List.range' 2816 128) = some 32491 := by
  decide +kernel
theorem leaf_block_2944 : walk 32 Artifact.commitCode leafWords 32491 (List.range' 2944 128) = some 33903 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
