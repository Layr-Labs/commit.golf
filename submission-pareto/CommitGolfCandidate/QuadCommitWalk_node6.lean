import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n3s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 4 (p % 4)) 180646 (List.range' 512 488) = some 182110 := by
  decide +kernel
theorem n3r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 4 (p % 4)) 182112 (List.range' 0 218) = some 182766 := by
  decide +kernel
theorem n4s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 182783 (List.range' 0 512) = some 184319 := by
  decide +kernel
theorem n4s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 184319 (List.range' 512 488) = some 185783 := by
  decide +kernel
theorem n4r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 185785 (List.range' 0 512) = some 187321 := by
  decide +kernel
theorem n4r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 187321 (List.range' 512 43) = some 187450 := by
  decide +kernel
theorem n5s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 187463 (List.range' 0 512) = some 188999 := by
  decide +kernel
theorem n5s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 188999 (List.range' 512 488) = some 190463 := by
  decide +kernel
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 190465 (List.range' 0 512) = some 192001 := by
  decide +kernel
theorem n5r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192001 (List.range' 512 266) = some 192799 := by
  decide +kernel
theorem n6s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192808 (List.range' 0 512) = some 194344 := by
  decide +kernel
theorem n6s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 194344 (List.range' 512 488) = some 195808 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 195810 (List.range' 0 389) = some 196977 := by
  decide +kernel
theorem n7s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 196990 (List.range' 0 512) = some 198526 := by
  decide +kernel
theorem n7s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 198526 (List.range' 512 488) = some 199990 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
