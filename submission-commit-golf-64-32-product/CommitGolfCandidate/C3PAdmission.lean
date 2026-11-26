import CommitGolfCandidate.C3PCommitFacts
import CommitGolfCandidate.TwoPermutationPackedCertificate
import CommitGolfCandidate.TwoPermutationPackedOpeningABI

/-! # The paired submission's admission, opener ABI and commit layout (kept apart: the image checks
are the memory-heavy part of the assembly). -/
namespace TwoPermutationPrototype.PackedCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling

-- Sequential elaboration: the official verifier's build crashed here (Lean exit 139, no output) with
-- parallel elaboration on two CPUs; a local `lean -j 1` run reproduced the crash.
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev pairedSubmission : Submission := Artifact.submission

theorem paired_admitted : pairedSubmission.Admission := by
  intro program
  cases program <;>
    simp only [pairedSubmission, Artifact.submission, Image.Valid, Image.byteSize, LayoutValid,
      dataBase, ArtifactEncoding.length_decode] <;> decide

theorem paired_opening_abi : PackedOpening.OpeningABI pairedSubmission where
  toOpeningLayout := ⟨rfl, rfl, rfl, rfl⟩
  image := rfl
  capacity := by decide
  fuel := by decide

theorem paired_commit_layout : RV64.C3P.PairedCommitLayout pairedSubmission where
  image := RV64.packed_manifest_image.symm
  fuel := by decide
  message := rfl
  commitment := rfl
  trapdoor := rfl

end TwoPermutationPrototype.PackedCertificate
