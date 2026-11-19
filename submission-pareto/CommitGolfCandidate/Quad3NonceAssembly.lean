import CommitGolfCandidate.Quad3NonceCertificate
import CommitGolfCandidate.QuadOpeningTranscript
import CommitGolfCandidate.Quad3NonceSecurity

/-! Quad3 + NonceChain certificate assembly. Inputs: the quad3 opening ABI, the commit side's
`Quad3NonceCommitTranscript`, its resource fact, and the quad3 checker facts. -/
namespace TwoPermutationPrototype.Quad3NonceCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuadCertificate (CheckerFacts)

set_option autoImplicit false

theorem quad3_nonce_opening_facts (s : Submission) (abi : QuadOpening.OpeningABI s)
    (commit : Quad3NonceCommitTranscript s) : OpeningFacts s 107901 81408 where
  runs trapdoor positions := by
    obtain ⟨result, run, physical⟩ := QuadOpening.opening_physical s abi trapdoor positions
    have successful := QuadOpening.opening_success s abi trapdoor positions result physical
    refine ⟨result, run, physical.success, successful, fun batch => ?_⟩
    have limits := QuadOpening.opening_scored_limits s trapdoor positions result physical batch
    have length := QuadOpening.opening_proof_size s abi trapdoor positions result physical
    exact ⟨limits.1, length.trans_le limits.2⟩
  refines := QuadOpening.transcript_refines s abi commit

/-- Quad3 + NonceChain certificate for any commit cycle count the commit image proves. -/
theorem quad3_nonce_certificate (s : Submission) (admitted : s.Admission) (abi : QuadOpening.OpeningABI s)
    (commit : Quad3NonceCommitTranscript s) (commitCycles : Nat)
    (resources : ∀ (message : Message) (result : Execution), result ∈ support (s.run .commit message) →
      result.exit = .success ∧ result.cycles = commitCycles ∧ result.oracleCalls ≤ COMMIT_BUDGET)
    (checks : CheckerFacts s) :
    Certificate s 81408 commitCycles 107901 :=
  let opens := quad3_nonce_opening_facts s abi commit
  certificate_of_facts resources admitted opens checks
    (quad3_nonce_hiding s.scheme opens.refines)

end TwoPermutationPrototype.Quad3NonceCertificate
