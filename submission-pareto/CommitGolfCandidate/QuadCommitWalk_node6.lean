import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n5s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 188326 (List.range' 0 512) = some 189862 := by
  decide +kernel
theorem n5s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 189862 (List.range' 512 488) = some 191326 := by
  decide +kernel
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 191328 (List.range' 0 422) = some 192594 := by
  decide +kernel
theorem n6s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192603 (List.range' 0 512) = some 194139 := by
  decide +kernel
theorem n6s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 194139 (List.range' 512 488) = some 195603 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 195605 (List.range' 0 512) = some 197141 := by
  decide +kernel
theorem n6r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 197141 (List.range' 512 199) = some 197738 := by
  decide +kernel
theorem n7s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 197751 (List.range' 0 512) = some 199287 := by
  decide +kernel
theorem n7s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 199287 (List.range' 512 488) = some 200751 := by
  decide +kernel
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 200753 (List.range' 0 356) = some 201821 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 201830 (List.range' 0 512) = some 203366 := by
  decide +kernel
theorem n8r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203366 (List.range' 512 512) = some 204902 := by
  decide +kernel
theorem n8r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 204902 (List.range' 1024 512) = some 206438 := by
  decide +kernel
theorem n8r_block_1536 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 206438 (List.range' 1536 142) = some 206864 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 206873 (List.range' 0 512) = some 208409 := by
  decide +kernel
theorem n9r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 208409 (List.range' 512 327) = some 209390 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
