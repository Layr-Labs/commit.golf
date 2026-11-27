import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n5s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 187653 (List.range' 512 488) = some 189117 := by
  decide +kernel
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 189119 (List.range' 0 512) = some 190655 := by
  decide +kernel
theorem n5r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 190655 (List.range' 512 43) = some 190784 := by
  decide +kernel
theorem n6s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 190797 (List.range' 0 512) = some 192333 := by
  decide +kernel
theorem n6s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192333 (List.range' 512 488) = some 193797 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 193799 (List.range' 0 512) = some 195335 := by
  decide +kernel
theorem n6r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 195335 (List.range' 512 266) = some 196133 := by
  decide +kernel
theorem n7s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 196142 (List.range' 0 512) = some 197678 := by
  decide +kernel
theorem n7s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 197678 (List.range' 512 488) = some 199142 := by
  decide +kernel
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 199144 (List.range' 0 389) = some 200311 := by
  decide +kernel
theorem n8s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 200324 (List.range' 0 512) = some 201860 := by
  decide +kernel
theorem n8s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 201860 (List.range' 512 488) = some 203324 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203326 (List.range' 0 195) = some 203911 := by
  decide +kernel
theorem n9s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203924 (List.range' 0 512) = some 205460 := by
  decide +kernel
theorem n9s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 205460 (List.range' 512 488) = some 206924 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 206926 (List.range' 0 98) = some 207220 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
