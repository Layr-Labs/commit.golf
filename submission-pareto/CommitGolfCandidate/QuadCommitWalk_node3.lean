import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n1s_block_23040 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 114346 (List.range' 23040 512) = some 115882 := by
  decide +kernel
theorem n1s_block_23552 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 115882 (List.range' 23552 512) = some 117418 := by
  decide +kernel
theorem n1s_block_24064 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 117418 (List.range' 24064 512) = some 118954 := by
  decide +kernel
theorem n1s_block_24576 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 118954 (List.range' 24576 512) = some 120490 := by
  decide +kernel
theorem n1s_block_25088 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 120490 (List.range' 25088 512) = some 122026 := by
  decide +kernel
theorem n1s_block_25600 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 122026 (List.range' 25600 512) = some 123562 := by
  decide +kernel
theorem n1s_block_26112 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 123562 (List.range' 26112 512) = some 125098 := by
  decide +kernel
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
theorem n2s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 134803 (List.range' 0 512) = some 136339 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
