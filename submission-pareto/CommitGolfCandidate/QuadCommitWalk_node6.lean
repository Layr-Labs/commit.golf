import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n2s_block_12800 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 173203 (List.range' 12800 512) = some 174739 := by
  decide +kernel
theorem n2s_block_13312 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 174739 (List.range' 13312 512) = some 176275 := by
  decide +kernel
theorem n2s_block_13824 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 176275 (List.range' 13824 512) = some 177811 := by
  decide +kernel
theorem n2s_block_14336 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 177811 (List.range' 14336 249) = some 178558 := by
  decide +kernel
theorem n2r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 178560 (List.range' 0 179) = some 179097 := by
  decide +kernel
theorem n3s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 179110 (List.range' 0 512) = some 180646 := by
  decide +kernel
theorem n3s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 180646 (List.range' 512 488) = some 182110 := by
  decide +kernel
theorem n3r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 182112 (List.range' 0 218) = some 182766 := by
  decide +kernel
theorem n4s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 182783 (List.range' 0 512) = some 184319 := by
  decide +kernel
theorem n4s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 184319 (List.range' 512 488) = some 185783 := by
  decide +kernel
theorem n4r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 185785 (List.range' 0 512) = some 187321 := by
  decide +kernel
theorem n4r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 187321 (List.range' 512 332) = some 188317 := by
  decide +kernel
theorem n5s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 188330 (List.range' 0 512) = some 189866 := by
  decide +kernel
theorem n5s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 189866 (List.range' 512 487) = some 191327 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
