import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_4096 : walk 32 Artifact.commitCode (fun _ => parentWords) 110759 (List.range' 4096 512) = some 112807 := by
  decide +kernel
theorem parent_block_4608 : walk 32 Artifact.commitCode (fun _ => parentWords) 112807 (List.range' 4608 512) = some 114855 := by
  decide +kernel
theorem parent_block_5120 : walk 32 Artifact.commitCode (fun _ => parentWords) 114855 (List.range' 5120 512) = some 116903 := by
  decide +kernel
theorem parent_block_5632 : walk 32 Artifact.commitCode (fun _ => parentWords) 116903 (List.range' 5632 512) = some 118951 := by
  decide +kernel
theorem parent_block_6144 : walk 32 Artifact.commitCode (fun _ => parentWords) 118951 (List.range' 6144 512) = some 120999 := by
  decide +kernel
theorem parent_block_6656 : walk 32 Artifact.commitCode (fun _ => parentWords) 120999 (List.range' 6656 512) = some 123047 := by
  decide +kernel
theorem parent_block_7168 : walk 32 Artifact.commitCode (fun _ => parentWords) 123047 (List.range' 7168 512) = some 125095 := by
  decide +kernel
theorem parent_block_7680 : walk 32 Artifact.commitCode (fun _ => parentWords) 125095 (List.range' 7680 512) = some 127143 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
