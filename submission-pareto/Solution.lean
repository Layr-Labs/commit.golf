import CommitGolfCandidate.QuadArtifactSubmission
import CommitGolfCandidate.PentaCounterCertificate
import CommitGolfCandidate.QuadCheckerComplete

namespace CommitGolf.Challenge
open TwoPermutationPrototype
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling

set_option maxRecDepth 65536

def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

theorem checker_facts : QuadCertificate.CapCheckerFacts submission := by
  rw [show submission = _ from QuadCertificate.artifact_is_quad]
  exact Quad.Checker.checker_facts _ rfl rfl rfl rfl

theorem certificate : CommitGolf.Certificate submission 99072 473011392 62859 := by
  have commit : PentaGrouped.PentaCounterCommitTranscript submission := by
    rw [show submission = _ from QuadCertificate.artifact_is_quad]
    exact PentaGrouped.penta_counter_commit_transcript QuadOpening.openingImage Quad.Checker.quadCheckImage
  have resources : ∀ (message : Message) (result : Execution), result ∈ support (submission.run .commit message) →
      result.exit = .success ∧ result.cycles = 473011392 ∧ result.oracleCalls ≤ COMMIT_BUDGET := by
    rw [show submission = _ from QuadCertificate.artifact_is_quad]
    exact PentaGrouped.commit_resources QuadOpening.openingImage Quad.Checker.quadCheckImage
  exact PentaCounterCertificate.penta_counter_certificate submission QuadCertificate.quad_admitted
    QuadCertificate.quad_opening_abi commit 473011392 resources checker_facts

end CommitGolf.Challenge
