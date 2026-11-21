import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem qtwo_block_0 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 94375 (List.range' 0 128) = some 95911 := by
  decide +kernel
theorem qtwo_block_128 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 95911 (List.range' 128 128) = some 97447 := by
  decide +kernel
theorem qtwo_block_256 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 97447 (List.range' 256 128) = some 98983 := by
  decide +kernel
theorem qtwo_block_384 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 98983 (List.range' 384 128) = some 100519 := by
  decide +kernel
theorem qtwo_block_512 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 100519 (List.range' 512 128) = some 102055 := by
  decide +kernel
theorem qtwo_block_640 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 102055 (List.range' 640 128) = some 103591 := by
  decide +kernel
theorem qtwo_block_768 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 103591 (List.range' 768 128) = some 105127 := by
  decide +kernel
theorem qtwo_block_896 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 105127 (List.range' 896 128) = some 106663 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
