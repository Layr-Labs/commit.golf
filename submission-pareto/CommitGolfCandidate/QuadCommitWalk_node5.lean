import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n2s_block_8192 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 159379 (List.range' 8192 512) = some 160915 := by
  decide +kernel
theorem n2s_block_8704 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 160915 (List.range' 8704 512) = some 162451 := by
  decide +kernel
theorem n2s_block_9216 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 162451 (List.range' 9216 512) = some 163987 := by
  decide +kernel
theorem n2s_block_9728 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 163987 (List.range' 9728 512) = some 165523 := by
  decide +kernel
theorem n2s_block_10240 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 165523 (List.range' 10240 512) = some 167059 := by
  decide +kernel
theorem n2s_block_10752 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 167059 (List.range' 10752 512) = some 168595 := by
  decide +kernel
theorem n2s_block_11264 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 168595 (List.range' 11264 512) = some 170131 := by
  decide +kernel
theorem n2s_block_11776 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 170131 (List.range' 11776 512) = some 171667 := by
  decide +kernel
theorem n2s_block_12288 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 171667 (List.range' 12288 512) = some 173203 := by
  decide +kernel
theorem n2s_block_12800 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 173203 (List.range' 12800 512) = some 174739 := by
  decide +kernel
theorem n2s_block_13312 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 174739 (List.range' 13312 512) = some 176275 := by
  decide +kernel
theorem n2s_block_13824 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 176275 (List.range' 13824 512) = some 177811 := by
  decide +kernel
theorem n2s_block_14336 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 177811 (List.range' 14336 249) = some 178558 := by
  decide +kernel
theorem n2r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 178560 (List.range' 0 179) = some 179097 := by
  decide +kernel
theorem n3s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 179110 (List.range' 0 512) = some 180646 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
