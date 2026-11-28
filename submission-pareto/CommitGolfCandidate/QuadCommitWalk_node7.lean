import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 3 (p % 3)) 191329 (List.range' 0 374) = some 192451 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192464 (List.range' 0 512) = some 194000 := by
  decide +kernel
theorem n6r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 194000 (List.range' 512 512) = some 195536 := by
  decide +kernel
theorem n6r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 195536 (List.range' 1024 512) = some 197072 := by
  decide +kernel
theorem n6r_block_1536 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 197072 (List.range' 1536 254) = some 197834 := by
  decide +kernel
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 197843 (List.range' 0 512) = some 199379 := by
  decide +kernel
theorem n7r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 199379 (List.range' 512 383) = some 200528 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 200541 (List.range' 0 448) = some 201885 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 201894 (List.range' 0 224) = some 202566 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 202579 (List.range' 0 45) = some 202714 := by
  decide +kernel
theorem n11r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 202723 (List.range' 0 9) = some 202750 := by
  decide +kernel
theorem n12r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 202763 (List.range' 0 2) = some 202769 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
