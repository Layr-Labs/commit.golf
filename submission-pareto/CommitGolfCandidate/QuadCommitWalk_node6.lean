import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n6r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 161095 (List.range' 512 451) = some 162448 := by
  decide +kernel
theorem n7s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 162461 (List.range' 0 512) = some 163997 := by
  decide +kernel
theorem n7s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 163997 (List.range' 512 488) = some 165461 := by
  decide +kernel
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 165463 (List.range' 0 512) = some 166999 := by
  decide +kernel
theorem n7r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 166999 (List.range' 512 470) = some 168409 := by
  decide +kernel
theorem n8s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 168418 (List.range' 0 512) = some 169954 := by
  decide +kernel
theorem n8s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 169954 (List.range' 512 488) = some 171418 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 171420 (List.range' 0 512) = some 172956 := by
  decide +kernel
theorem n8r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 172956 (List.range' 512 479) = some 174393 := by
  decide +kernel
theorem n9s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 174406 (List.range' 0 512) = some 175942 := by
  decide +kernel
theorem n9s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 175942 (List.range' 512 488) = some 177406 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 177408 (List.range' 0 496) = some 178896 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 178905 (List.range' 0 512) = some 180441 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
