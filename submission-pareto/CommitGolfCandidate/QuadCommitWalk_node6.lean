import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n7s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 160873 (List.range' 0 512) = some 162409 := by
  decide +kernel
theorem n7s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 162409 (List.range' 512 488) = some 163873 := by
  decide +kernel
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 163875 (List.range' 0 486) = some 165333 := by
  decide +kernel
theorem n8s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 165342 (List.range' 0 512) = some 166878 := by
  decide +kernel
theorem n8s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 166878 (List.range' 512 488) = some 168342 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 168344 (List.range' 0 243) = some 169073 := by
  decide +kernel
theorem n9s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 169086 (List.range' 0 512) = some 170622 := by
  decide +kernel
theorem n9s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 170622 (List.range' 512 488) = some 172086 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 172088 (List.range' 0 512) = some 173624 := by
  decide +kernel
theorem n9r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 173624 (List.range' 512 110) = some 173954 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 173963 (List.range' 0 512) = some 175499 := by
  decide +kernel
theorem n10r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 175499 (List.range' 512 512) = some 177035 := by
  decide +kernel
theorem n10r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 177035 (List.range' 1024 287) = some 177896 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
