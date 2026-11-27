import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 168517 (List.range' 0 486) = some 169975 := by
  decide +kernel
theorem n9s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 169984 (List.range' 0 512) = some 171520 := by
  decide +kernel
theorem n9s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 171520 (List.range' 512 488) = some 172984 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 172986 (List.range' 0 243) = some 173715 := by
  decide +kernel
theorem n10s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 173728 (List.range' 0 512) = some 175264 := by
  decide +kernel
theorem n10s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 175264 (List.range' 512 488) = some 176728 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 176730 (List.range' 0 512) = some 178266 := by
  decide +kernel
theorem n10r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 178266 (List.range' 512 110) = some 178596 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 178605 (List.range' 0 512) = some 180141 := by
  decide +kernel
theorem n11r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 180141 (List.range' 512 512) = some 181677 := by
  decide +kernel
theorem n11r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 181677 (List.range' 1024 287) = some 182538 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 182551 (List.range' 0 512) = some 184087 := by
  decide +kernel
theorem n12r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 184087 (List.range' 512 144) = some 184519 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 184528 (List.range' 0 328) = some 185512 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
