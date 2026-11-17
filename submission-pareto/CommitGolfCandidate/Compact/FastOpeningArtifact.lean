import CommitGolf.Artifact
import CommitGolfCandidate.Compact.FastOpeningSubmission
import CommitGolfCandidate.PackedImageEquality
/-! Full artifact equality for the unrolled compact opening and the retained compact checker. -/
namespace CommitGolfCandidate.Compact
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem fast_submission_matches : fastSubmission=Artifact.submission := by
  have images : fastSubmission.image=Artifact.submission.image := by
    funext program
    cases program with
    | commit =>
      change (⟨group341ImageWords,[]⟩ : Riscv.Image)=
        ⟨ArtifactEncoding.decode 32 Artifact.commitCode,ArtifactEncoding.decode 8 Artifact.commitData⟩
      exact congrArg (fun code => (⟨code,[]⟩ : Riscv.Image)) packed_code_matches_image
    | opening => rfl
    | check => rfl
  change (Submission.mk fastSubmission.sizes fastSubmission.layout fastSubmission.image fastSubmission.steps)=
    (Submission.mk fastSubmission.sizes fastSubmission.layout Artifact.submission.image fastSubmission.steps)
  exact congrArg (fun image => Submission.mk fastSubmission.sizes fastSubmission.layout image fastSubmission.steps) images
end CommitGolfCandidate.Compact
