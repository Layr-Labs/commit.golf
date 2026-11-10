import CommitGolf.Artifact
import CommitGolfCandidate.Compact.NoInitSubmission
import CommitGolfCandidate.PackedImageEquality
/-! Full artifact equality for the unrolled compact opening and the retained compact checker. -/
namespace CommitGolfCandidate.Compact
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem noInit_submission_matches : noInitSubmission=Artifact.submission := by
  have images : noInitSubmission.image=Artifact.submission.image := by
    funext program
    cases program with
    | commit =>
      change (⟨group341ImageWords,[]⟩ : Riscv.Image)=
        ⟨ArtifactEncoding.decode 32 Artifact.commitCode,ArtifactEncoding.decode 8 Artifact.commitData⟩
      exact congrArg (fun code => (⟨code,[]⟩ : Riscv.Image)) packed_code_matches_image
    | opening => rfl
    | check => rfl
  change (Submission.mk noInitSubmission.sizes noInitSubmission.layout noInitSubmission.image noInitSubmission.steps)=
    (Submission.mk noInitSubmission.sizes noInitSubmission.layout Artifact.submission.image noInitSubmission.steps)
  exact congrArg (fun image => Submission.mk noInitSubmission.sizes noInitSubmission.layout image noInitSubmission.steps) images
end CommitGolfCandidate.Compact
