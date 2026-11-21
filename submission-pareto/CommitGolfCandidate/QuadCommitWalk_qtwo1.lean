import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem qtwo_block_1024 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 106663 (List.range' 1024 128) = some 108199 := by
  decide +kernel
theorem qtwo_block_1152 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 108199 (List.range' 1152 128) = some 109735 := by
  decide +kernel
theorem qtwo_block_1280 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 109735 (List.range' 1280 128) = some 111271 := by
  decide +kernel
theorem qtwo_block_1408 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 111271 (List.range' 1408 128) = some 112807 := by
  decide +kernel
theorem qtwo_block_1536 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 112807 (List.range' 1536 128) = some 114343 := by
  decide +kernel
theorem qtwo_block_1664 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 114343 (List.range' 1664 128) = some 115879 := by
  decide +kernel
theorem qtwo_block_1792 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 115879 (List.range' 1792 128) = some 117415 := by
  decide +kernel
theorem qtwo_block_1920 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 117415 (List.range' 1920 128) = some 118951 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
