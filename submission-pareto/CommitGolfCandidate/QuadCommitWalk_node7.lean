import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 199992 (List.range' 0 195) = some 200577 := by
  decide +kernel
theorem n8s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 200590 (List.range' 0 512) = some 202126 := by
  decide +kernel
theorem n8s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 202126 (List.range' 512 488) = some 203590 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203592 (List.range' 0 98) = some 203886 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203895 (List.range' 0 512) = some 205431 := by
  decide +kernel
theorem n9r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 205431 (List.range' 512 512) = some 206967 := by
  decide +kernel
theorem n9r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 206967 (List.range' 1024 25) = some 207042 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 207055 (List.range' 0 512) = some 208591 := by
  decide +kernel
theorem n10r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 208591 (List.range' 512 13) = some 208630 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 208643 (List.range' 0 263) = some 209432 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 209449 (List.range' 0 53) = some 209608 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 209625 (List.range' 0 11) = some 209658 := by
  decide +kernel
theorem n14r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 209683 (List.range' 0 3) = some 209692 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
