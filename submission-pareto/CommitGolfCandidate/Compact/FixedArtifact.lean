import CommitGolf.Artifact
import CommitGolfCandidate.Compact.FixedSubmission
import CommitGolfCandidate.PackedImageEquality
/-! Full artifact equality for the unrolled compact opening and the retained compact checker. -/
namespace CommitGolfCandidate.Compact
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem fixed_submission_matches : fixedSubmission=Artifact.submission := by
  have images : fixedSubmission.image=Artifact.submission.image := by
    funext program
    cases program with
    | commit =>
      change (⟨group341ImageWords,[]⟩ : Riscv.Image)=
        ⟨ArtifactEncoding.decode 32 Artifact.commitCode,ArtifactEncoding.decode 8 Artifact.commitData⟩
      exact congrArg (fun code => (⟨code,[]⟩ : Riscv.Image)) packed_code_matches_image
    | opening => rfl
    | check => rfl
  change (Submission.mk fixedSubmission.sizes fixedSubmission.layout fixedSubmission.image fixedSubmission.steps)=
    (Submission.mk fixedSubmission.sizes fixedSubmission.layout Artifact.submission.image fixedSubmission.steps)
  exact congrArg (fun image => Submission.mk fixedSubmission.sizes fixedSubmission.layout image fixedSubmission.steps) images
end CommitGolfCandidate.Compact
