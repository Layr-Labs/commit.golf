import CommitGolf.Artifact
import CommitGolfCandidate.TwoPermutationCheckerWide

namespace TwoPermutationPrototype.WideCertificate
open CommitGolf TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

theorem artifact_checker_image :
    Artifact.submission.image .check = Checker.checkerImage := by
  unfold Artifact.submission Checker.checkerImage
  congr 1 <;> decide

/-- Instantiate the exact checker refinement using the verifier's artifact. -/
theorem artifact_checker_facts : CheckerFacts Artifact.submission :=
  verified_checker Artifact.submission rfl rfl artifact_checker_image rfl

end TwoPermutationPrototype.WideCertificate
