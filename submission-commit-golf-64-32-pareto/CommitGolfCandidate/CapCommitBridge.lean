import CommitGolfCandidate.CapExperimentalABI
import CommitGolfCandidate.CommitSemantics

/-! The cap candidate retains the certified commitment image and its ABI.
Equality is scoped to commitment execution and serialization; the opening
and checker images have separate initial states and separate proofs. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_commit_run_same (message : Message) :
    capProgram.run .commit message = submission.run .commit message := by
  rfl

theorem cap_commit_read_same (result : Execution) :
    capProgram.readCommit result = submission.readCommit result := by
  rfl

theorem cap_commit_matches (oracle : Oracle) (message : Message)
    (committed : Execution × Nat)
    (reachable : committed ∈ support (oracle.run (capProgram.run .commit message))) :
    CommittedState oracle message committed.1.state := by
  rw [cap_commit_run_same] at reachable
  exact commit_run_matches oracle message committed reachable

end CommitGolfCandidate
