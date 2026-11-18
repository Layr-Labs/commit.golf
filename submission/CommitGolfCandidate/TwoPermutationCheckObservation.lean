import CommitGolfCandidate.TwoPermutationCheckLoader
import CommitGolfCandidate.TwoPermutationCheckerReplay

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling

theorem check_observation_admitted (oracle : Oracle) (input : CheckInput)
    (admitted : input.proof.length ≤ QAssembly.submission.sizes.proof) :
    checkObservation QAssembly.submission oracle input =
      checkEvaluation oracle (recordRows
        (execute (QAssembly.submission.image .check) 34359803904 (QAssembly.submission.initialState .check input) false)) := by
  unfold checkObservation
  erw [check_run_admitted input admitted]

theorem check_observation_oversized (oracle : Oracle) (input : CheckInput)
    (oversized : QAssembly.submission.sizes.proof < input.proof.length) :
    checkObservation QAssembly.submission oracle input = ((⟨.failure,initialMachine,0,0⟩,[]),0) := by
  unfold checkObservation
  erw [check_run_oversized input oversized]
  rw [record_rows_pure, check_evaluation_pure]

end TwoPermutationPrototype.Checker
