import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem qtwo_block_3072 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 131239 (List.range' 3072 128) = some 132775 := by
  decide +kernel
theorem qtwo_block_3200 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 132775 (List.range' 3200 128) = some 134311 := by
  decide +kernel
theorem qtwo_block_3328 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 134311 (List.range' 3328 128) = some 135847 := by
  decide +kernel
theorem qtwo_block_3456 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 135847 (List.range' 3456 128) = some 137383 := by
  decide +kernel
theorem qtwo_block_3584 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 137383 (List.range' 3584 128) = some 138919 := by
  decide +kernel
theorem qtwo_block_3712 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 138919 (List.range' 3712 128) = some 140455 := by
  decide +kernel
theorem qtwo_block_3840 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 140455 (List.range' 3840 128) = some 141991 := by
  decide +kernel
theorem qtwo_block_3968 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 141991 (List.range' 3968 128) = some 143527 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
