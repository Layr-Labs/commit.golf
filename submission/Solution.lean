import CommitGolfCandidate.QuadArtifactSubmission
import CommitGolfCandidate.QuadNonceAssembly
import CommitGolfCandidate.QuadCheckerComplete
import CommitGolfCandidate.QuadNonceCommitTranscript

namespace CommitGolf.Challenge
open TwoPermutationPrototype
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling

set_option maxRecDepth 65536

def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

theorem checker_facts : QuadCertificate.CheckerFacts submission := by
  rw [show submission = _ from QuadCertificate.artifact_is_quad]
  exact Quad.Checker.checker_facts _ rfl rfl rfl rfl

theorem certificate : CommitGolf.Certificate submission 72192 522460577 94841 := by
  have commit : QuadNonceCommitTranscript submission := by
    rw [show submission = _ from QuadCertificate.artifact_is_quad]; exact Quad.Commit.verifiedNonceTranscript QuadOpening.openingImage Quad.Checker.quadCheckImage
  have resources : ∀ (message : Message) (result : Execution), result ∈ support (submission.run .commit message) →
      result.exit = .success ∧ result.cycles = 522460577 ∧ result.oracleCalls ≤ COMMIT_BUDGET := by
    rw [show submission = _ from QuadCertificate.artifact_is_quad]; exact Quad.Commit.nonce_commit_resources QuadOpening.openingImage Quad.Checker.quadCheckImage
  exact QuadNonceCertificate.quad_nonce_certificate submission QuadCertificate.quad_admitted
    QuadCertificate.quad_opening_abi commit 522460577 resources checker_facts

end CommitGolf.Challenge
