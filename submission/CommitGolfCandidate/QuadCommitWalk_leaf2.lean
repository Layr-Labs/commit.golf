import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_2048 : walk 32 Artifact.commitCode leafWords 22601 (List.range' 2048 128) = some 24013 := by
  decide +kernel
theorem leaf_block_2176 : walk 32 Artifact.commitCode leafWords 24013 (List.range' 2176 128) = some 25424 := by
  decide +kernel
theorem leaf_block_2304 : walk 32 Artifact.commitCode leafWords 25424 (List.range' 2304 128) = some 26836 := by
  decide +kernel
theorem leaf_block_2432 : walk 32 Artifact.commitCode leafWords 26836 (List.range' 2432 128) = some 28247 := by
  decide +kernel
theorem leaf_block_2560 : walk 32 Artifact.commitCode leafWords 28247 (List.range' 2560 128) = some 29659 := by
  decide +kernel
theorem leaf_block_2688 : walk 32 Artifact.commitCode leafWords 29659 (List.range' 2688 128) = some 31070 := by
  decide +kernel
theorem leaf_block_2816 : walk 32 Artifact.commitCode leafWords 31070 (List.range' 2816 128) = some 32481 := by
  decide +kernel
theorem leaf_block_2944 : walk 32 Artifact.commitCode leafWords 32481 (List.range' 2944 128) = some 33892 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
