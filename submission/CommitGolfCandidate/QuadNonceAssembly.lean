import CommitGolfCandidate.QuadNonceCertificate
import CommitGolfCandidate.QuadOpeningTranscript
import CommitGolfCandidate.QuadNonceSecurity

/-! Quad + NonceChain certificate assembly (replaces `QuadAssembly` once the commit image runs the
nonce chain). Inputs: the opening ABI (unchanged), the commit side's `QuadNonceCommitTranscript`,
its resource fact, and the unchanged checker facts. -/
namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open CommitGolfCandidate.Permutation.NoncePair (Key actualNonces)
local instance nonceOpeningDiscrete {α : Type} : MeasurableSpace α := ⊤

/-- The unchanged quad opener composed with the seed-keyed commit distribution. -/
theorem nonce_transcript_refines (s : Submission) (abi : OpeningABI s) (commit : QuadNonceCommitTranscript s) :
    QuadNonceTranscriptRefines s.scheme quadTranscriptBuilder := by
  intro oracle message positions
  unfold executableTranscript
  rw [fixed_oracle_run_bind]
  apply ((commit.distribution oracle message).bind_left _).trans
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro k
  rw [scheme_open_bytes s abi, pure_bind, fixed_oracle_run_pure]
  have proof := proof_from_trapdoor_matches s (commit.trapdoor oracle message k) positions
    oracle.compression (quadFunction oracle.permutation)
    (quadPublicLeaves oracle message (actualNonces oracle.permutation k)) (actualNonces oracle.permutation k)
    (fun node lo hi => commit.heap oracle message k node lo hi)
    (fun index => commit.leaf oracle message k index)
    (fun index => commit.nonce oracle message k index)
  rw [proof]
  rfl

end TwoPermutationPrototype.QuadOpening

namespace TwoPermutationPrototype.QuadNonceCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuadCertificate (CheckerFacts)

set_option autoImplicit false

theorem quad_nonce_opening_facts (s : Submission) (abi : QuadOpening.OpeningABI s)
    (commit : QuadNonceCommitTranscript s) : OpeningFacts s where
  runs trapdoor positions := by
    obtain ⟨result, run, physical⟩ := QuadOpening.opening_physical s abi trapdoor positions
    have successful := QuadOpening.opening_success s abi trapdoor positions result physical
    refine ⟨result, run, physical.success, successful, fun batch => ?_⟩
    have limits := QuadOpening.opening_scored_limits s trapdoor positions result physical batch
    have length := QuadOpening.opening_proof_size s abi trapdoor positions result physical
    exact ⟨limits.1, length.trans_le limits.2⟩
  refines := QuadOpening.nonce_transcript_refines s abi commit

/-- Quad + NonceChain certificate. `commitCycles` is whatever the nonce commit image proves
(prediction ≈ 523.3M); the call count only needs `≤ COMMIT_BUDGET` (it is 43,468,287). -/
theorem quad_nonce_certificate (s : Submission) (admitted : s.Admission) (abi : QuadOpening.OpeningABI s)
    (commit : QuadNonceCommitTranscript s) (commitCycles : Nat)
    (resources : ∀ (message : Message) (result : Execution), result ∈ support (s.run .commit message) →
      result.exit = .success ∧ result.cycles = commitCycles ∧ result.oracleCalls ≤ COMMIT_BUDGET)
    (checks : CheckerFacts s) :
    Certificate s 72192 commitCycles 94841 :=
  let opens := quad_nonce_opening_facts s abi commit
  certificate_of_facts resources admitted opens checks
    (quad_nonce_hiding s.scheme opens.refines)

end TwoPermutationPrototype.QuadNonceCertificate
