import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 201691 (List.range' 0 237) = some 202402 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 202415 (List.range' 0 512) = some 203951 := by
  decide +kernel
theorem n8r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203951 (List.range' 512 512) = some 205487 := by
  decide +kernel
theorem n8r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 205487 (List.range' 1024 95) = some 205772 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 205785 (List.range' 0 512) = some 207321 := by
  decide +kernel
theorem n9r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 207321 (List.range' 512 48) = some 207465 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 207474 (List.range' 0 280) = some 208314 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 208323 (List.range' 0 56) = some 208491 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 208516 (List.range' 0 12) = some 208552 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 208573 (List.range' 0 3) = some 208582 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
