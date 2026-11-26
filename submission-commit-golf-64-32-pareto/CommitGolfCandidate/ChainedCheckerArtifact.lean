import CommitGolfCandidate.ChainedCheckerControllerFetch
import CommitGolf.Artifact

/-! Exact equality with the officially rendered delivered checking image. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checking_manifest_code :
    ArtifactEncoding.decode 32 Artifact.checkCode=chainedCheckerImage.code := by decide +kernel

theorem checking_manifest_image : Artifact.submission.image .check=chainedCheckerImage := by
  change Image.mk (ArtifactEncoding.decode 32 Artifact.checkCode) (ArtifactEncoding.decode 8 Artifact.checkData)=
    Image.mk chainedCheckerImage.code chainedCheckerImage.data
  exact congrArg₂ Image.mk checking_manifest_code (by rfl)

end CommitGolfCandidate.Chained.Native
