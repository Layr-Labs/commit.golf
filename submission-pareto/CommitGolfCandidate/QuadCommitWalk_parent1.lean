import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_3584 : walk 32 Artifact.commitCode (fun _ => parentWords) 207037 (List.range' 3584 512) = some 209085 := by
  decide +kernel
theorem parent_block_4096 : walk 32 Artifact.commitCode (fun _ => parentWords) 209085 (List.range' 4096 512) = some 211133 := by
  decide +kernel
theorem parent_block_4608 : walk 32 Artifact.commitCode (fun _ => parentWords) 211133 (List.range' 4608 512) = some 213181 := by
  decide +kernel
theorem parent_block_5120 : walk 32 Artifact.commitCode (fun _ => parentWords) 213181 (List.range' 5120 512) = some 215229 := by
  decide +kernel
theorem parent_block_5632 : walk 32 Artifact.commitCode (fun _ => parentWords) 215229 (List.range' 5632 512) = some 217277 := by
  decide +kernel
theorem parent_block_6144 : walk 32 Artifact.commitCode (fun _ => parentWords) 217277 (List.range' 6144 512) = some 219325 := by
  decide +kernel
theorem parent_block_6656 : walk 32 Artifact.commitCode (fun _ => parentWords) 219325 (List.range' 6656 512) = some 221373 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
