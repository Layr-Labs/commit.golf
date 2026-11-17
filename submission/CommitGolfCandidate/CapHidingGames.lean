import CommitGolfCandidate.CapHidingReduction
import CommitGolfCandidate.CapOldOpeningHeap
import CommitGolfCandidate.CapCommitBridge
import CommitGolfCandidate.CapOpenProgramRun

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv OracleComp
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

theorem cap_open_commit_postprocess (message : Message) (committed : Execution)
    (positions : Positions) :
    capProgram.scheme.opening (capProgram.readCommit committed).2 positions =
      capPostprocess positions <$>
        submission.scheme.opening (submission.readCommit committed).2 positions := by
  rw [opening_scheme_execution,map_pure]
  by_cases empty : positions.card=0
  · rw [cap_open_empty_scheme_bytes _ _ empty,cap_postprocess_empty _ _ empty]
  · have positive := Nat.pos_of_ne_zero empty
    rw [cap_open_nonempty_scheme_bytes _ _ positive]
    apply congrArg (pure : Proof → OracleComp World Proof)
    exact (cap_postprocess_old_opening message committed.state positions positive).symm

private theorem commit_map (program : Submission) (message : Message) :
    program.scheme.commit message=program.readCommit <$> program.run .commit message := rfl

theorem cap_hiding_experiment_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    Hiding.hidingExperiment capProgram.scheme adversary selectSecond =
      Hiding.hidingExperiment submission.scheme
        (capTransformAdversary capPostprocess adversary) selectSecond := by
  unfold Hiding.hidingExperiment
  simp only [capTransformAdversary,bind_map_left,capLiftHidingChallenge]
  apply bind_congr
  intro challenge
  erw [commit_map]
  erw [bind_map_left,bind_map_left]
  apply bind_congr
  intro committed
  erw [cap_open_commit_postprocess
    (if selectSecond then challenge.message₁ else challenge.message₀),bind_map_left]
  rfl

end CommitGolfCandidate
