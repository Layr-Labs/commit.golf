import CommitGolfCandidate.QuadCertificate
import CommitGolfCandidate.QuadOpeningTranscript
import CommitGolfCandidate.QuadHiding

/-! Assembly of the quad certificate from its three independent parts:
the commit transcript and resource fact (commit image), the opening facts (opening image, proved here
from `QuadOpening`), the checker facts (check image) and the quad hiding reduction. -/
namespace TwoPermutationPrototype.QuadCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling

set_option autoImplicit false

theorem quad_opening_facts (s : Submission) (abi : QuadOpening.OpeningABI s) (commit : QuadCommitTranscript s) :
    OpeningFacts s where
  runs trapdoor positions := by
    obtain ⟨result, run, physical⟩ := QuadOpening.opening_physical s abi trapdoor positions
    have successful := QuadOpening.opening_success s abi trapdoor positions result physical
    refine ⟨result, run, physical.success, successful, fun batch => ?_⟩
    have limits := QuadOpening.opening_scored_limits s trapdoor positions result physical batch
    have length := QuadOpening.opening_proof_size s abi trapdoor positions result physical
    exact ⟨limits.1, length.trans_le limits.2⟩
  refines := QuadOpening.transcript_refines s abi commit

theorem quad_certificate (s : Submission) (admitted : s.Admission) (abi : QuadOpening.OpeningABI s)
    (commit : QuadCommitTranscript s)
    (resources : ∀ (message : Message) (result : Execution), result ∈ support (s.run .commit message) →
      result.exit = .success ∧ result.cycles = 541525048 ∧ result.oracleCalls = 41943039)
    (checks : CheckerFacts s) :
    Certificate s 72192 541525048 94841 :=
  let opens := quad_opening_facts s abi commit
  certificate_of_facts resources admitted opens checks
    (quad_hiding_of_transcript s.scheme quadTranscriptBuilder opens.refines)

end TwoPermutationPrototype.QuadCertificate
