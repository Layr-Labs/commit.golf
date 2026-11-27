import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 191332 (List.range' 0 369) = some 192439 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192452 (List.range' 0 512) = some 193988 := by
  decide +kernel
theorem n6r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 193988 (List.range' 512 512) = some 195524 := by
  decide +kernel
theorem n6r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 195524 (List.range' 1024 50) = some 195674 := by
  decide +kernel
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 195683 (List.range' 0 512) = some 197219 := by
  decide +kernel
theorem n7r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 197219 (List.range' 512 25) = some 197294 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 197307 (List.range' 0 269) = some 198114 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 198127 (List.range' 0 54) = some 198289 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 198302 (List.range' 0 11) = some 198335 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 198360 (List.range' 0 3) = some 198369 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
