import CommitGolfCandidate.Quad2NonceCertificate
import CommitGolfCandidate.QuadOpeningTranscript
import CommitGolfCandidate.Quad2NonceSecurity

/-! Quad2 + NonceChain certificate assembly. Inputs: the quad2 opening ABI, the commit side's
`Quad2NonceCommitTranscript`, its resource fact, and the quad2 checker facts. -/
namespace TwoPermutationPrototype.Quad2NonceCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuadCertificate (CheckerFacts)

set_option autoImplicit false

theorem quad2_nonce_opening_facts (s : Submission) (abi : QuadOpening.OpeningABI s)
    (commit : Quad2NonceCommitTranscript s) : OpeningFacts s 101371 76800 where
  runs trapdoor positions := by
    obtain ⟨result, run, physical⟩ := QuadOpening.opening_physical s abi trapdoor positions
    have successful := QuadOpening.opening_success s abi trapdoor positions result physical
    refine ⟨result, run, physical.success, successful, fun batch => ?_⟩
    have limits := QuadOpening.opening_scored_limits s trapdoor positions result physical batch
    have length := QuadOpening.opening_proof_size s abi trapdoor positions result physical
    exact ⟨limits.1, length.trans_le limits.2⟩
  refines := QuadOpening.transcript_refines s abi commit

/-- Quad2 + NonceChain certificate for any commit cycle count the commit image proves. -/
theorem quad2_nonce_certificate (s : Submission) (admitted : s.Admission) (abi : QuadOpening.OpeningABI s)
    (commit : Quad2NonceCommitTranscript s) (commitCycles : Nat)
    (resources : ∀ (message : Message) (result : Execution), result ∈ support (s.run .commit message) →
      result.exit = .success ∧ result.cycles = commitCycles ∧ result.oracleCalls ≤ COMMIT_BUDGET)
    (checks : CheckerFacts s) :
    Certificate s 76800 commitCycles 101371 :=
  let opens := quad2_nonce_opening_facts s abi commit
  certificate_of_facts resources admitted opens checks
    (quad2_nonce_hiding s.scheme opens.refines)

end TwoPermutationPrototype.Quad2NonceCertificate
