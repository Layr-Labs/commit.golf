import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 207229 (List.range' 0 512) = some 208765 := by
  decide +kernel
theorem n10r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 208765 (List.range' 512 512) = some 210301 := by
  decide +kernel
theorem n10r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 210301 (List.range' 1024 25) = some 210376 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 210389 (List.range' 0 512) = some 211925 := by
  decide +kernel
theorem n11r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 211925 (List.range' 512 13) = some 211964 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 211977 (List.range' 0 263) = some 212766 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 212779 (List.range' 0 132) = some 213175 := by
  decide +kernel
theorem n14r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 213184 (List.range' 0 66) = some 213382 := by
  decide +kernel
theorem n15r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 213391 (List.range' 0 33) = some 213490 := by
  decide +kernel
theorem n16r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 213503 (List.range' 0 17) = some 213554 := by
  decide +kernel
theorem n17r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 213567 (List.range' 0 9) = some 213594 := by
  decide +kernel
theorem n18r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 213607 (List.range' 0 5) = some 213622 := by
  decide +kernel
theorem n19r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 213635 (List.range' 0 3) = some 213644 := by
  decide +kernel
theorem n20r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 213657 (List.range' 0 2) = some 213663 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
