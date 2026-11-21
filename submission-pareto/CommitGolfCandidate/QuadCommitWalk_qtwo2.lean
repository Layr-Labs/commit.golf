import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem qtwo_block_2048 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 118951 (List.range' 2048 128) = some 120487 := by
  decide +kernel
theorem qtwo_block_2176 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 120487 (List.range' 2176 128) = some 122023 := by
  decide +kernel
theorem qtwo_block_2304 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 122023 (List.range' 2304 128) = some 123559 := by
  decide +kernel
theorem qtwo_block_2432 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 123559 (List.range' 2432 128) = some 125095 := by
  decide +kernel
theorem qtwo_block_2560 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 125095 (List.range' 2560 128) = some 126631 := by
  decide +kernel
theorem qtwo_block_2688 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 126631 (List.range' 2688 128) = some 128167 := by
  decide +kernel
theorem qtwo_block_2816 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 128167 (List.range' 2816 128) = some 129703 := by
  decide +kernel
theorem qtwo_block_2944 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 129703 (List.range' 2944 128) = some 131239 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
