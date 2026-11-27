import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n1s_block_26624 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 125098 (List.range' 26624 512) = some 126634 := by
  decide +kernel
theorem n1s_block_27136 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 126634 (List.range' 27136 512) = some 128170 := by
  decide +kernel
theorem n1s_block_27648 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 128170 (List.range' 27648 512) = some 129706 := by
  decide +kernel
theorem n1s_block_28160 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 129706 (List.range' 28160 512) = some 131242 := by
  decide +kernel
theorem n1s_block_28672 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 131242 (List.range' 28672 512) = some 132778 := by
  decide +kernel
theorem n1s_block_29184 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 132778 (List.range' 29184 246) = some 133516 := by
  decide +kernel
theorem n1r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 133518 (List.range' 0 424) = some 134790 := by
  decide +kernel
theorem n2s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 134803 (List.range' 0 512) = some 136339 := by
  decide +kernel
theorem n2s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 136339 (List.range' 512 487) = some 137800 := by
  decide +kernel
theorem n2r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 137802 (List.range' 0 512) = some 139338 := by
  decide +kernel
theorem n2r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 139338 (List.range' 512 248) = some 140082 := by
  decide +kernel
theorem n3s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 140099 (List.range' 0 512) = some 141635 := by
  decide +kernel
theorem n3s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 141635 (List.range' 512 488) = some 143099 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
