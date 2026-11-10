import CommitGolf.Artifact
import CommitGolfCandidate.Compact.NoJumpSubmission
import CommitGolfCandidate.PackedImageEquality
/-! Full artifact equality for the unrolled compact opening and the retained compact checker. -/
namespace CommitGolfCandidate.Compact
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem noJump_submission_matches : noJumpSubmission=Artifact.submission := by
  have images : noJumpSubmission.image=Artifact.submission.image := by
    funext program
    cases program with
    | commit =>
      change (⟨group341ImageWords,[]⟩ : Riscv.Image)=
        ⟨ArtifactEncoding.decode 32 Artifact.commitCode,ArtifactEncoding.decode 8 Artifact.commitData⟩
      exact congrArg (fun code => (⟨code,[]⟩ : Riscv.Image)) packed_code_matches_image
    | opening => rfl
    | check => rfl
  change (Submission.mk noJumpSubmission.sizes noJumpSubmission.layout noJumpSubmission.image noJumpSubmission.steps)=
    (Submission.mk noJumpSubmission.sizes noJumpSubmission.layout Artifact.submission.image noJumpSubmission.steps)
  exact congrArg (fun image => Submission.mk noJumpSubmission.sizes noJumpSubmission.layout image noJumpSubmission.steps) images
end CommitGolfCandidate.Compact
