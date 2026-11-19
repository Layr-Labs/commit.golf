import CommitGolfCandidate.QuadArtifactSubmission
import CommitGolfCandidate.Quad2NonceAssembly
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

theorem certificate : CommitGolf.Certificate submission 76800 499194978 101371 := by
  have commit : Quad2NonceCommitTranscript submission := by
    rw [show submission = _ from QuadCertificate.artifact_is_quad]; exact Quad.Commit.verifiedNonceTranscript QuadOpening.openingImage Quad.Checker.quadCheckImage
  have resources : ∀ (message : Message) (result : Execution), result ∈ support (submission.run .commit message) →
      result.exit = .success ∧ result.cycles = 499194978 ∧ result.oracleCalls ≤ COMMIT_BUDGET := by
    rw [show submission = _ from QuadCertificate.artifact_is_quad]; exact Quad.Commit.nonce_commit_resources QuadOpening.openingImage Quad.Checker.quadCheckImage
  exact Quad2NonceCertificate.quad2_nonce_certificate submission QuadCertificate.quad_admitted
    QuadCertificate.quad_opening_abi commit 499194978 resources checker_facts

end CommitGolf.Challenge
