import CommitGolf.Artifact
import CommitGolfCandidate.Compact.Programs
import CommitGolfCandidate.PackedImageEquality

/-! Full equality between the certified compact-format images and the independently
rendered artifact. The commitment equality checks its complete packed byte image. -/
namespace CommitGolfCandidate.Compact
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem submission_matches : submission=Artifact.submission := by
  have images : submission.image=Artifact.submission.image := by
    funext program
    cases program with
    | commit =>
      change (⟨group341ImageWords,[]⟩ : Riscv.Image)=
        ⟨ArtifactEncoding.decode 32 Artifact.commitCode,ArtifactEncoding.decode 8 Artifact.commitData⟩
      exact congrArg (fun code => (⟨code,[]⟩ : Riscv.Image)) packed_code_matches_image
    | opening => rfl
    | check => rfl
  change (Submission.mk submission.sizes submission.layout submission.image submission.steps)=
    (Submission.mk submission.sizes submission.layout Artifact.submission.image submission.steps)
  exact congrArg (fun image => Submission.mk submission.sizes submission.layout image submission.steps) images
end CommitGolfCandidate.Compact
