import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem qtwo_block_12288 : walk 32 Artifact.commitCode (fun _ => quadWords) 131239 (List.range' 12288 512) = some 132775 := by
  decide +kernel
theorem qtwo_block_12800 : walk 32 Artifact.commitCode (fun _ => quadWords) 132775 (List.range' 12800 512) = some 134311 := by
  decide +kernel
theorem qtwo_block_13312 : walk 32 Artifact.commitCode (fun _ => quadWords) 134311 (List.range' 13312 512) = some 135847 := by
  decide +kernel
theorem qtwo_block_13824 : walk 32 Artifact.commitCode (fun _ => quadWords) 135847 (List.range' 13824 512) = some 137383 := by
  decide +kernel
theorem qtwo_block_14336 : walk 32 Artifact.commitCode (fun _ => quadWords) 137383 (List.range' 14336 512) = some 138919 := by
  decide +kernel
theorem qtwo_block_14848 : walk 32 Artifact.commitCode (fun _ => quadWords) 138919 (List.range' 14848 512) = some 140455 := by
  decide +kernel
theorem qtwo_block_15360 : walk 32 Artifact.commitCode (fun _ => quadWords) 140455 (List.range' 15360 512) = some 141991 := by
  decide +kernel
theorem qtwo_block_15872 : walk 32 Artifact.commitCode (fun _ => quadWords) 141991 (List.range' 15872 512) = some 143527 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
