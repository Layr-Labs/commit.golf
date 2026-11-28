import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n10r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 180441 (List.range' 512 512) = some 181977 := by
  decide +kernel
theorem n10r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 181977 (List.range' 1024 512) = some 183513 := by
  decide +kernel
theorem n10r_block_1536 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 183513 (List.range' 1536 212) = some 184149 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 184158 (List.range' 0 512) = some 185694 := by
  decide +kernel
theorem n11r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 185694 (List.range' 512 362) = some 186780 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 186789 (List.range' 0 437) = some 188100 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 188113 (List.range' 0 219) = some 188770 := by
  decide +kernel
theorem n14r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 188783 (List.range' 0 44) = some 188915 := by
  decide +kernel
theorem n15r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 188928 (List.range' 0 9) = some 188955 := by
  decide +kernel
theorem n16r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 188968 (List.range' 0 2) = some 188974 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
