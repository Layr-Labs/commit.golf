import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem qtwo_block_8192 : walk 32 Artifact.commitCode (fun _ => quadWords) 118951 (List.range' 8192 512) = some 120487 := by
  decide +kernel
theorem qtwo_block_8704 : walk 32 Artifact.commitCode (fun _ => quadWords) 120487 (List.range' 8704 512) = some 122023 := by
  decide +kernel
theorem qtwo_block_9216 : walk 32 Artifact.commitCode (fun _ => quadWords) 122023 (List.range' 9216 512) = some 123559 := by
  decide +kernel
theorem qtwo_block_9728 : walk 32 Artifact.commitCode (fun _ => quadWords) 123559 (List.range' 9728 512) = some 125095 := by
  decide +kernel
theorem qtwo_block_10240 : walk 32 Artifact.commitCode (fun _ => quadWords) 125095 (List.range' 10240 512) = some 126631 := by
  decide +kernel
theorem qtwo_block_10752 : walk 32 Artifact.commitCode (fun _ => quadWords) 126631 (List.range' 10752 512) = some 128167 := by
  decide +kernel
theorem qtwo_block_11264 : walk 32 Artifact.commitCode (fun _ => quadWords) 128167 (List.range' 11264 512) = some 129703 := by
  decide +kernel
theorem qtwo_block_11776 : walk 32 Artifact.commitCode (fun _ => quadWords) 129703 (List.range' 11776 512) = some 131239 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
