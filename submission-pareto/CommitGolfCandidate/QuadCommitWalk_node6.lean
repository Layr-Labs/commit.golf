import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n3s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 180646 (List.range' 512 488) = some 182110 := by
  decide +kernel
theorem n3r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 182112 (List.range' 0 218) = some 182766 := by
  decide +kernel
theorem n4s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 182783 (List.range' 0 512) = some 184319 := by
  decide +kernel
theorem n4s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 184319 (List.range' 512 487) = some 185780 := by
  decide +kernel
theorem n4r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 185782 (List.range' 0 512) = some 187318 := by
  decide +kernel
theorem n4r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 187318 (List.range' 512 358) = some 188392 := by
  decide +kernel
theorem n5s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 188401 (List.range' 0 512) = some 189937 := by
  decide +kernel
theorem n5s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 189937 (List.range' 512 488) = some 191401 := by
  decide +kernel
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 191403 (List.range' 0 512) = some 192939 := by
  decide +kernel
theorem n5r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192939 (List.range' 512 436) = some 194247 := by
  decide +kernel
theorem n6s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 194256 (List.range' 0 512) = some 195792 := by
  decide +kernel
theorem n6s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 195792 (List.range' 512 488) = some 197256 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 197258 (List.range' 0 474) = some 198680 := by
  decide +kernel
theorem n7s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 198689 (List.range' 0 512) = some 200225 := by
  decide +kernel
theorem n7s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 200225 (List.range' 512 488) = some 201689 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
