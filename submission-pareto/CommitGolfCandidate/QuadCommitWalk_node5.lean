import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n3r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 143101 (List.range' 0 512) = some 144637 := by
  decide +kernel
theorem n3r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 144637 (List.range' 512 185) = some 145192 := by
  decide +kernel
theorem n4s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 145205 (List.range' 0 512) = some 146741 := by
  decide +kernel
theorem n4s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 146741 (List.range' 512 488) = some 148205 := by
  decide +kernel
theorem n4r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 148207 (List.range' 0 512) = some 149743 := by
  decide +kernel
theorem n4r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 149743 (List.range' 512 337) = some 150754 := by
  decide +kernel
theorem n5s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 150767 (List.range' 0 512) = some 152303 := by
  decide +kernel
theorem n5s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 152303 (List.range' 512 488) = some 153767 := by
  decide +kernel
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 153769 (List.range' 0 512) = some 155305 := by
  decide +kernel
theorem n5r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 155305 (List.range' 512 413) = some 156544 := by
  decide +kernel
theorem n6s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 156557 (List.range' 0 512) = some 158093 := by
  decide +kernel
theorem n6s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 158093 (List.range' 512 488) = some 159557 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 159559 (List.range' 0 512) = some 161095 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
