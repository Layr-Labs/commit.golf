import CommitGolfCandidate.C3POpeningFacts
import CommitGolfCandidate.C3PCheckerFacts
import CommitGolfCandidate.C3PHidingScheme

/-! # The paired submission's certificate

The checker runs the paired leaf block (`c3pBlock`) and the leader's lower steps; the opener runs the
pre-pass and the leader's records; the commit runs the paired leaf blocks and parents. -/
namespace TwoPermutationPrototype.PackedCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling

-- Sequential elaboration, as in C3PAdmission (the verifier builds with parallel elaboration on two CPUs).
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem paired_certificate : Certificate pairedSubmission 67489 1267884575 91600 :=
  certificate_of_facts paired_commit_resources paired_admitted paired_opening_facts
    (Packed.Checker.paired_checker_facts Hybrid.c3p_replay_bound238)
    (scheme_hiding_of_c3p_transcript pairedSubmission.scheme Hybrid.wireBuilder paired_opening_facts.refines)

end TwoPermutationPrototype.PackedCertificate
