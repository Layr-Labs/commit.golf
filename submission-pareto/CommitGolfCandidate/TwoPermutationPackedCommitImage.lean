import CommitGolf.Artifact

/-! Shared delivered image, independent of either internal-parent proof chain. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv

def packedWideCommitImage : Image :=
  ⟨ArtifactEncoding.decode 32 Artifact.commitCode,ArtifactEncoding.decode 8 Artifact.commitData⟩

theorem packed_manifest_image : packedWideCommitImage = Artifact.submission.image .commit := by
  simp only [packedWideCommitImage,Artifact.submission]

end TwoPermutationPrototype.RV64
