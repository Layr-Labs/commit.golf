import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem pair_block_0 : walk 32 Artifact.commitCode (fun _ => pairWords) 157228 (List.range' 0 512) = some 159788 := by
  decide +kernel
theorem pair_block_512 : walk 32 Artifact.commitCode (fun _ => pairWords) 159788 (List.range' 512 512) = some 162348 := by
  decide +kernel
theorem pair_block_1024 : walk 32 Artifact.commitCode (fun _ => pairWords) 162348 (List.range' 1024 512) = some 164908 := by
  decide +kernel
theorem pair_block_1536 : walk 32 Artifact.commitCode (fun _ => pairWords) 164908 (List.range' 1536 512) = some 167468 := by
  decide +kernel
theorem pair_block_2048 : walk 32 Artifact.commitCode (fun _ => pairWords) 167468 (List.range' 2048 512) = some 170028 := by
  decide +kernel
theorem pair_block_2560 : walk 32 Artifact.commitCode (fun _ => pairWords) 170028 (List.range' 2560 512) = some 172588 := by
  decide +kernel
theorem pair_block_3072 : walk 32 Artifact.commitCode (fun _ => pairWords) 172588 (List.range' 3072 512) = some 175148 := by
  decide +kernel
theorem pair_block_3584 : walk 32 Artifact.commitCode (fun _ => pairWords) 175148 (List.range' 3584 512) = some 177708 := by
  decide +kernel
theorem pair_block_4096 : walk 32 Artifact.commitCode (fun _ => pairWords) 177708 (List.range' 4096 512) = some 180268 := by
  decide +kernel
theorem pair_block_4608 : walk 32 Artifact.commitCode (fun _ => pairWords) 180268 (List.range' 4608 512) = some 182828 := by
  decide +kernel
theorem pair_block_5120 : walk 32 Artifact.commitCode (fun _ => pairWords) 182828 (List.range' 5120 512) = some 185388 := by
  decide +kernel
theorem pair_block_5632 : walk 32 Artifact.commitCode (fun _ => pairWords) 185388 (List.range' 5632 512) = some 187948 := by
  decide +kernel
theorem pair_block_6144 : walk 32 Artifact.commitCode (fun _ => pairWords) 187948 (List.range' 6144 512) = some 190508 := by
  decide +kernel
theorem pair_block_6656 : walk 32 Artifact.commitCode (fun _ => pairWords) 190508 (List.range' 6656 512) = some 193068 := by
  decide +kernel
theorem pair_block_7168 : walk 32 Artifact.commitCode (fun _ => pairWords) 193068 (List.range' 7168 512) = some 195628 := by
  decide +kernel
theorem pair_block_7680 : walk 32 Artifact.commitCode (fun _ => pairWords) 195628 (List.range' 7680 512) = some 198188 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
