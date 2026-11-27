import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n1s_block_28672 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 131242 (List.range' 28672 512) = some 132778 := by
  decide +kernel
theorem n1s_block_29184 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 132778 (List.range' 29184 246) = some 133516 := by
  decide +kernel
theorem n1r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 133518 (List.range' 0 424) = some 134790 := by
  decide +kernel
theorem n2s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 134803 (List.range' 0 512) = some 136339 := by
  decide +kernel
theorem n2s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 136339 (List.range' 512 488) = some 137803 := by
  decide +kernel
theorem n2r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 137805 (List.range' 0 89) = some 138072 := by
  decide +kernel
theorem n3s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 138085 (List.range' 0 512) = some 139621 := by
  decide +kernel
theorem n3s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 139621 (List.range' 512 488) = some 141085 := by
  decide +kernel
theorem n3r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 141087 (List.range' 0 512) = some 142623 := by
  decide +kernel
theorem n3r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 142623 (List.range' 512 33) = some 142722 := by
  decide +kernel
theorem n4s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 142735 (List.range' 0 512) = some 144271 := by
  decide +kernel
theorem n4s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 144271 (List.range' 512 488) = some 145735 := by
  decide +kernel
theorem n4r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 145737 (List.range' 0 512) = some 147273 := by
  decide +kernel
theorem n4r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 147273 (List.range' 512 261) = some 148056 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
