import CommitGolf.Artifact
import CommitGolfCandidate.Compact.SlimSubmission
import CommitGolfCandidate.PackedImageEquality
/-! Full artifact equality for the unrolled compact opening and the retained compact checker. -/
namespace CommitGolfCandidate.Compact
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem slim_submission_matches : slimSubmission=Artifact.submission := by
  have images : slimSubmission.image=Artifact.submission.image := by
    funext program
    cases program with
    | commit =>
      change (⟨group341ImageWords,[]⟩ : Riscv.Image)=
        ⟨ArtifactEncoding.decode 32 Artifact.commitCode,ArtifactEncoding.decode 8 Artifact.commitData⟩
      exact congrArg (fun code => (⟨code,[]⟩ : Riscv.Image)) packed_code_matches_image
    | opening => rfl
    | check => rfl
  change (Submission.mk slimSubmission.sizes slimSubmission.layout slimSubmission.image slimSubmission.steps)=
    (Submission.mk slimSubmission.sizes slimSubmission.layout Artifact.submission.image slimSubmission.steps)
  exact congrArg (fun image => Submission.mk slimSubmission.sizes slimSubmission.layout image slimSubmission.steps) images
end CommitGolfCandidate.Compact
