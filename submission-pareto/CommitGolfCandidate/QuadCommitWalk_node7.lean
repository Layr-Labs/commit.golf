import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n7r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 200642 (List.range' 512 81) = some 200885 := by
  decide +kernel
theorem n8s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 200898 (List.range' 0 512) = some 202434 := by
  decide +kernel
theorem n8s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 202434 (List.range' 512 488) = some 203898 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203900 (List.range' 0 512) = some 205436 := by
  decide +kernel
theorem n8r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 205436 (List.range' 512 285) = some 206291 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 206304 (List.range' 0 512) = some 207840 := by
  decide +kernel
theorem n9r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 207840 (List.range' 512 512) = some 209376 := by
  decide +kernel
theorem n9r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 209376 (List.range' 1024 375) = some 210501 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 210514 (List.range' 0 512) = some 212050 := by
  decide +kernel
theorem n10r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 212050 (List.range' 512 188) = some 212614 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 212623 (List.range' 0 350) = some 213673 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 213682 (List.range' 0 175) = some 214207 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 214220 (List.range' 0 88) = some 214484 := by
  decide +kernel
theorem n14r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 214501 (List.range' 0 18) = some 214555 := by
  decide +kernel
theorem n15r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 214572 (List.range' 0 4) = some 214584 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
