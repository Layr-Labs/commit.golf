import CommitGolfCandidate.HidingDistribution
import CommitGolfCandidate.HidingSecurity

/-! Statistical hiding of the submitted images. The transcript law
(`HidingDistribution`) identifies the submitted game with the reference game with
generated nonces, played by the adversary that applies the compaction pass to the
proof it observes; that adversary keeps the shared query budget, and the reference
games are within the contract's error for every adversary (`reference_hiding_bound`,
`HidingSecurity`). Both adaptive stages, their shared query budget and the common
sampled oracle remain intact. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option autoImplicit false

/-- Hiding for the actual RISC-V commitment and opening images, at the contract's
error function. No separate simulator, efficiency axiom, or abstract scheme is assumed. -/
theorem nonce_compressed_hiding : nonceCompressedProgram.scheme.Hiding HIDING_ERROR :=
  s3_submission_hiding honest_transcript_law fun adversary bounded =>
    reference_hiding_bound adversary bounded

end CommitGolfCandidate
