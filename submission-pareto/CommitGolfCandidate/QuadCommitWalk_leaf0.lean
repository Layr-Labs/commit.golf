import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_0 : walk 32 Artifact.commitCode leafWords 19 (List.range' 0 128) = some 1430 := by
  decide +kernel
theorem leaf_block_128 : walk 32 Artifact.commitCode leafWords 1430 (List.range' 128 128) = some 2842 := by
  decide +kernel
theorem leaf_block_256 : walk 32 Artifact.commitCode leafWords 2842 (List.range' 256 128) = some 4254 := by
  decide +kernel
theorem leaf_block_384 : walk 32 Artifact.commitCode leafWords 4254 (List.range' 384 128) = some 5666 := by
  decide +kernel
theorem leaf_block_512 : walk 32 Artifact.commitCode leafWords 5666 (List.range' 512 128) = some 7078 := by
  decide +kernel
theorem leaf_block_640 : walk 32 Artifact.commitCode leafWords 7078 (List.range' 640 128) = some 8490 := by
  decide +kernel
theorem leaf_block_768 : walk 32 Artifact.commitCode leafWords 8490 (List.range' 768 128) = some 9901 := by
  decide +kernel
theorem leaf_block_896 : walk 32 Artifact.commitCode leafWords 9901 (List.range' 896 128) = some 11313 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
