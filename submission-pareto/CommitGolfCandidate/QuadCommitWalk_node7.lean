import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n7r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 200594 (List.range' 1024 319) = some 201551 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 201564 (List.range' 0 512) = some 203100 := by
  decide +kernel
theorem n8r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203100 (List.range' 512 160) = some 203580 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203589 (List.range' 0 336) = some 204597 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 204606 (List.range' 0 168) = some 205110 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 205127 (List.range' 0 34) = some 205229 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 205242 (List.range' 0 7) = some 205263 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 205284 (List.range' 0 2) = some 205290 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
