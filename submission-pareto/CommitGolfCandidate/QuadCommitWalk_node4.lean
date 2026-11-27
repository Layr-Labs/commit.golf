import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n2s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 136339 (List.range' 512 512) = some 137875 := by
  decide +kernel
theorem n2s_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 137875 (List.range' 1024 512) = some 139411 := by
  decide +kernel
theorem n2s_block_1536 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 139411 (List.range' 1536 512) = some 140947 := by
  decide +kernel
theorem n2s_block_2048 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 140947 (List.range' 2048 512) = some 142483 := by
  decide +kernel
theorem n2s_block_2560 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 142483 (List.range' 2560 512) = some 144019 := by
  decide +kernel
theorem n2s_block_3072 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 144019 (List.range' 3072 512) = some 145555 := by
  decide +kernel
theorem n2s_block_3584 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 145555 (List.range' 3584 512) = some 147091 := by
  decide +kernel
theorem n2s_block_4096 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 147091 (List.range' 4096 512) = some 148627 := by
  decide +kernel
theorem n2s_block_4608 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 148627 (List.range' 4608 512) = some 150163 := by
  decide +kernel
theorem n2s_block_5120 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 150163 (List.range' 5120 512) = some 151699 := by
  decide +kernel
theorem n2s_block_5632 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 151699 (List.range' 5632 512) = some 153235 := by
  decide +kernel
theorem n2s_block_6144 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 153235 (List.range' 6144 512) = some 154771 := by
  decide +kernel
theorem n2s_block_6656 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 154771 (List.range' 6656 512) = some 156307 := by
  decide +kernel
theorem n2s_block_7168 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 156307 (List.range' 7168 512) = some 157843 := by
  decide +kernel
theorem n2s_block_7680 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 157843 (List.range' 7680 512) = some 159379 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
