import CommitGolfCandidate.CapHidingGames
import CommitGolfCandidate.HidingSecurity

/-! Statistical hiding of the actual cap images follows by exact experiment
equality and the retained full-path security theorem. Both adaptive stages,
their shared query budget and the common sampled oracle remain intact. -/
namespace CommitGolfCandidate
open CommitGolf
set_option autoImplicit false

theorem cap_program_hiding : capProgram.scheme.Hiding HIDING_ERROR := by
  constructor
  · exact submission_hiding.1
  · intro openingSize budget possible State Output adversary bounded
    have distance := submission_hiding.2 openingSize budget possible
      (State × Positions) Output (capTransformAdversary capPostprocess adversary)
      (cap_transform_query_bound capPostprocess adversary bounded)
    simpa only [← cap_hiding_experiment_eq] using distance

end CommitGolfCandidate
