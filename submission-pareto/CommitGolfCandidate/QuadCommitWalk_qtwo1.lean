import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem qtwo_block_4096 : walk 32 Artifact.commitCode (fun _ => quadWords) 106663 (List.range' 4096 512) = some 108199 := by
  decide +kernel
theorem qtwo_block_4608 : walk 32 Artifact.commitCode (fun _ => quadWords) 108199 (List.range' 4608 512) = some 109735 := by
  decide +kernel
theorem qtwo_block_5120 : walk 32 Artifact.commitCode (fun _ => quadWords) 109735 (List.range' 5120 512) = some 111271 := by
  decide +kernel
theorem qtwo_block_5632 : walk 32 Artifact.commitCode (fun _ => quadWords) 111271 (List.range' 5632 512) = some 112807 := by
  decide +kernel
theorem qtwo_block_6144 : walk 32 Artifact.commitCode (fun _ => quadWords) 112807 (List.range' 6144 512) = some 114343 := by
  decide +kernel
theorem qtwo_block_6656 : walk 32 Artifact.commitCode (fun _ => quadWords) 114343 (List.range' 6656 512) = some 115879 := by
  decide +kernel
theorem qtwo_block_7168 : walk 32 Artifact.commitCode (fun _ => quadWords) 115879 (List.range' 7168 512) = some 117415 := by
  decide +kernel
theorem qtwo_block_7680 : walk 32 Artifact.commitCode (fun _ => quadWords) 117415 (List.range' 7680 512) = some 118951 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
