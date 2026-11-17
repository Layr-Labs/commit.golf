import CommitGolfCandidate.CapHidingGames
import CommitGolfCandidate.HidingDistribution
import CommitGolfCandidate.HidingSecurity

/-! Statistical hiding of the submitted images. The machine transcript law
(`HidingDistribution`) identifies the real game with the stage-3 reference game,
whose distance is bounded by `reference_hiding_bound` (`HidingSecurity`). The cap
images follow by exact experiment equality. Both adaptive stages, their shared
query budget and the common sampled oracle remain intact. -/
namespace CommitGolfCandidate
open CommitGolf
set_option autoImplicit false

/-- Hiding for the actual RISC-V commitment and opening images, at the contract's
error function. No separate simulator, efficiency axiom, or abstract scheme is assumed. -/
theorem submission_hiding : submission.scheme.Hiding HIDING_ERROR :=
  s3_submission_hiding honest_transcript_law fun adversary bounded =>
    reference_hiding_bound adversary bounded

theorem cap_program_hiding : capProgram.scheme.Hiding HIDING_ERROR := by
  constructor
  · exact submission_hiding.1
  · intro openingSize budget possible State Output adversary bounded
    have distance := submission_hiding.2 openingSize budget possible
      (State × Positions) Output (capTransformAdversary capPostprocess adversary)
      (cap_transform_query_bound capPostprocess adversary bounded)
    simpa only [← cap_hiding_experiment_eq] using distance

end CommitGolfCandidate
