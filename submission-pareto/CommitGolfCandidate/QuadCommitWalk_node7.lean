import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 207229 (List.range' 0 512) = some 208765 := by
  decide +kernel
theorem n10r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 208765 (List.range' 512 512) = some 210301 := by
  decide +kernel
theorem n10r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 210301 (List.range' 1024 25) = some 210376 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 210389 (List.range' 0 512) = some 211925 := by
  decide +kernel
theorem n11r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 211925 (List.range' 512 13) = some 211964 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 211977 (List.range' 0 263) = some 212766 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 212783 (List.range' 0 53) = some 212942 := by
  decide +kernel
theorem n14r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 212959 (List.range' 0 11) = some 212992 := by
  decide +kernel
theorem n15r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 213017 (List.range' 0 3) = some 213026 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
