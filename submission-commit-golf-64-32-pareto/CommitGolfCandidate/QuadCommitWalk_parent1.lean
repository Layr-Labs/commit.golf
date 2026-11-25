import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem parent_block_3584 : walk 32 Artifact.commitCode (fun _ => parentWords) 157874 (List.range' 3584 512) = some 159922 := by
  decide +kernel
theorem parent_block_4096 : walk 32 Artifact.commitCode (fun _ => parentWords) 159922 (List.range' 4096 512) = some 161970 := by
  decide +kernel
theorem parent_block_4608 : walk 32 Artifact.commitCode (fun _ => parentWords) 161970 (List.range' 4608 512) = some 164018 := by
  decide +kernel
theorem parent_block_5120 : walk 32 Artifact.commitCode (fun _ => parentWords) 164018 (List.range' 5120 512) = some 166066 := by
  decide +kernel
theorem parent_block_5632 : walk 32 Artifact.commitCode (fun _ => parentWords) 166066 (List.range' 5632 512) = some 168114 := by
  decide +kernel
theorem parent_block_6144 : walk 32 Artifact.commitCode (fun _ => parentWords) 168114 (List.range' 6144 512) = some 170162 := by
  decide +kernel
theorem parent_block_6656 : walk 32 Artifact.commitCode (fun _ => parentWords) 170162 (List.range' 6656 512) = some 172210 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
