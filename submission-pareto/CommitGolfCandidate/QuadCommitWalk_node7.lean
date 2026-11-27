import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 4 (p % 4)) 191332 (List.range' 0 369) = some 192439 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192460 (List.range' 0 512) = some 193996 := by
  decide +kernel
theorem n6r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 193996 (List.range' 512 512) = some 195532 := by
  decide +kernel
theorem n6r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 195532 (List.range' 1024 319) = some 196489 := by
  decide +kernel
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 196502 (List.range' 0 512) = some 198038 := by
  decide +kernel
theorem n7r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 198038 (List.range' 512 160) = some 198518 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 198527 (List.range' 0 336) = some 199535 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 199544 (List.range' 0 168) = some 200048 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 200065 (List.range' 0 34) = some 200167 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 200180 (List.range' 0 7) = some 200201 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 200222 (List.range' 0 2) = some 200228 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
