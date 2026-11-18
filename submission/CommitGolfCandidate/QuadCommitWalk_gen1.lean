import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem pair_block_8192 : walk 32 Artifact.commitCode (fun _ => pairWords) 198188 (List.range' 8192 512) = some 200748 := by
  decide +kernel
theorem pair_block_8704 : walk 32 Artifact.commitCode (fun _ => pairWords) 200748 (List.range' 8704 512) = some 203308 := by
  decide +kernel
theorem pair_block_9216 : walk 32 Artifact.commitCode (fun _ => pairWords) 203308 (List.range' 9216 512) = some 205868 := by
  decide +kernel
theorem pair_block_9728 : walk 32 Artifact.commitCode (fun _ => pairWords) 205868 (List.range' 9728 512) = some 208428 := by
  decide +kernel
theorem pair_block_10240 : walk 32 Artifact.commitCode (fun _ => pairWords) 208428 (List.range' 10240 512) = some 210988 := by
  decide +kernel
theorem pair_block_10752 : walk 32 Artifact.commitCode (fun _ => pairWords) 210988 (List.range' 10752 512) = some 213548 := by
  decide +kernel
theorem pair_block_11264 : walk 32 Artifact.commitCode (fun _ => pairWords) 213548 (List.range' 11264 512) = some 216108 := by
  decide +kernel
theorem pair_block_11776 : walk 32 Artifact.commitCode (fun _ => pairWords) 216108 (List.range' 11776 512) = some 218668 := by
  decide +kernel
theorem pair_block_12288 : walk 32 Artifact.commitCode (fun _ => pairWords) 218668 (List.range' 12288 512) = some 221228 := by
  decide +kernel
theorem pair_block_12800 : walk 32 Artifact.commitCode (fun _ => pairWords) 221228 (List.range' 12800 512) = some 223788 := by
  decide +kernel
theorem pair_block_13312 : walk 32 Artifact.commitCode (fun _ => pairWords) 223788 (List.range' 13312 512) = some 226348 := by
  decide +kernel
theorem pair_block_13824 : walk 32 Artifact.commitCode (fun _ => pairWords) 226348 (List.range' 13824 512) = some 228908 := by
  decide +kernel
theorem pair_block_14336 : walk 32 Artifact.commitCode (fun _ => pairWords) 228908 (List.range' 14336 512) = some 231468 := by
  decide +kernel
theorem pair_block_14848 : walk 32 Artifact.commitCode (fun _ => pairWords) 231468 (List.range' 14848 512) = some 234028 := by
  decide +kernel
theorem pair_block_15360 : walk 32 Artifact.commitCode (fun _ => pairWords) 234028 (List.range' 15360 512) = some 236588 := by
  decide +kernel
theorem pair_block_15872 : walk 32 Artifact.commitCode (fun _ => pairWords) 236588 (List.range' 15872 16) = some 236668 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
