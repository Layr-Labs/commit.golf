import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_12288 : walk 32 Artifact.commitCode (fun _ => parentWords) 143527 (List.range' 12288 512) = some 145575 := by
  decide +kernel
theorem parent_block_12800 : walk 32 Artifact.commitCode (fun _ => parentWords) 145575 (List.range' 12800 512) = some 147623 := by
  decide +kernel
theorem parent_block_13312 : walk 32 Artifact.commitCode (fun _ => parentWords) 147623 (List.range' 13312 512) = some 149671 := by
  decide +kernel
theorem parent_block_13824 : walk 32 Artifact.commitCode (fun _ => parentWords) 149671 (List.range' 13824 512) = some 151719 := by
  decide +kernel
theorem parent_block_14336 : walk 32 Artifact.commitCode (fun _ => parentWords) 151719 (List.range' 14336 512) = some 153767 := by
  decide +kernel
theorem parent_block_14848 : walk 32 Artifact.commitCode (fun _ => parentWords) 153767 (List.range' 14848 512) = some 155815 := by
  decide +kernel
theorem parent_block_15360 : walk 32 Artifact.commitCode (fun _ => parentWords) 155815 (List.range' 15360 349) = some 157211 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
