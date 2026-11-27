import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n5s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 148069 (List.range' 0 512) = some 149605 := by
  decide +kernel
theorem n5s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 149605 (List.range' 512 488) = some 151069 := by
  decide +kernel
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 151071 (List.range' 0 512) = some 152607 := by
  decide +kernel
theorem n5r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 152607 (List.range' 512 375) = some 153732 := by
  decide +kernel
theorem n6s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 153745 (List.range' 0 512) = some 155281 := by
  decide +kernel
theorem n6s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 155281 (List.range' 512 488) = some 156745 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 156747 (List.range' 0 512) = some 158283 := by
  decide +kernel
theorem n6r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 158283 (List.range' 512 432) = some 159579 := by
  decide +kernel
theorem n7s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 159588 (List.range' 0 512) = some 161124 := by
  decide +kernel
theorem n7s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 161124 (List.range' 512 488) = some 162588 := by
  decide +kernel
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 162590 (List.range' 0 512) = some 164126 := by
  decide +kernel
theorem n7r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 164126 (List.range' 512 460) = some 165506 := by
  decide +kernel
theorem n8s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 165515 (List.range' 0 512) = some 167051 := by
  decide +kernel
theorem n8s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 167051 (List.range' 512 488) = some 168515 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
