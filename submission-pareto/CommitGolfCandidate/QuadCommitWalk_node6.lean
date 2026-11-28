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
theorem n4s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 4 (p % 4)) 182783 (List.range' 0 512) = some 184319 := by
  decide +kernel
theorem n4s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 4 (p % 4)) 184319 (List.range' 512 488) = some 185783 := by
  decide +kernel
theorem n4r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 4 (p % 4)) 185785 (List.range' 0 512) = some 187321 := by
  decide +kernel
theorem n4r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 4 (p % 4)) 187321 (List.range' 512 332) = some 188317 := by
  decide +kernel
theorem n5s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 188326 (List.range' 0 512) = some 189862 := by
  decide +kernel
theorem n5s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 189862 (List.range' 512 488) = some 191326 := by
  decide +kernel
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 191328 (List.range' 0 512) = some 192864 := by
  decide +kernel
theorem n5r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192864 (List.range' 512 199) = some 193461 := by
  decide +kernel
theorem n6s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 193474 (List.range' 0 512) = some 195010 := by
  decide +kernel
theorem n6s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 195010 (List.range' 512 488) = some 196474 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 196476 (List.range' 0 356) = some 197544 := by
  decide +kernel
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 197553 (List.range' 0 512) = some 199089 := by
  decide +kernel
theorem n7r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 199089 (List.range' 512 512) = some 200625 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
