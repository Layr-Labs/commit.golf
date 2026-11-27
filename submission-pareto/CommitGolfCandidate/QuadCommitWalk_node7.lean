import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n14r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 185521 (List.range' 0 164) = some 186013 := by
  decide +kernel
theorem n15r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 186026 (List.range' 0 33) = some 186125 := by
  decide +kernel
theorem n16r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 186142 (List.range' 0 7) = some 186163 := by
  decide +kernel
theorem n17r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 186184 (List.range' 0 2) = some 186190 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
