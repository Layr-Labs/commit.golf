import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n7r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 200625 (List.range' 1024 512) = some 202161 := by
  decide +kernel
theorem n7r_block_1536 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 202161 (List.range' 1536 142) = some 202587 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 202596 (List.range' 0 512) = some 204132 := by
  decide +kernel
theorem n8r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 204132 (List.range' 512 327) = some 205113 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 205126 (List.range' 0 420) = some 206386 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 206395 (List.range' 0 210) = some 207025 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 207034 (List.range' 0 42) = some 207160 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 207181 (List.range' 0 9) = some 207208 := by
  decide +kernel
theorem n13r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 207221 (List.range' 0 2) = some 207227 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
