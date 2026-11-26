import CommitGolfCandidate.TruncOpenInput
import CommitGolfCandidate.TruncRuntime
import CommitGolfCandidate.TruncImage
import CommitGolfCandidate.Machine

namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem honest_machine (candidate : Submission) (message : Message) (positions : Positions) :
    candidate.honestMachine message positions =
      (do let committed ← candidate.run .commit message
          let opened ← candidate.run .opening ((candidate.readCommit committed).2, positions)
          return ⟨committed.exit == Exit.success && candidate.openingSucceeded opened,
            committed.cycles, opened.cycles, (candidate.readProof opened).length⟩) := rfl

/-- Commitment success and opening success concern the same machine-derived scheme,
including the actual private trapdoor returned by commitment. -/
theorem honest_machine_resources (law : Wire.PackRun) (message : Message) (positions : Positions)
    (result : MachineResult) (reachable : result ∈ support (submission.honestMachine message positions)) :
    result.success = true ∧ result.commitCycles = 963641394 ∧
      result.openingCycles = Open.openingCycles positions.card := by
  rw [honest_machine] at reachable
  simp only [mem_support_bind_iff] at reachable
  obtain ⟨committed, committedReached, opened, openedReached, returned⟩ := reachable
  rw [Open.opening_execution law] at openedReached
  simp only [support_pure, Set.mem_singleton_iff] at openedReached returned
  subst opened
  subst result
  have committedResources := commit_input_resources message committed committedReached
  refine ⟨?_, committedResources.2.1, rfl⟩
  simp only [committedResources.1, beq_self_eq_true, Bool.true_and, Open.opening_result_succeeded]

/-- Both honest machine runs succeed with probability one for every message and
opening set. This proves the certificate's machine-success field. -/
theorem submission_machine_success (law : Wire.PackRun) : submission.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (honest_machine_resources law message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).1

/-- Certified upper bounds from the actual images for a complete commitment and a
128-leaf opening. These are the declared claim values, not a sampled measurement. -/
theorem submission_prover_cycles (law : Wire.PackRun) : submission.ProverCycles 963641394 109773 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have resources := honest_machine_resources law message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)
  rw [resources.2.1, resources.2.2, batch]
  decide

end CommitGolfCandidate.Trunc
