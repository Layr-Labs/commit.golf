import CommitGolfCandidate.CapCommitBridge
import CommitGolfCandidate.CapOpenResources
import CommitGolfCandidate.CapCheckOracleResources
import CommitGolfCandidate.Machine

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_program_termination : capProgram.Termination := by
  intro oracle program input
  cases program with
  | commit =>
    exact submission_termination oracle .commit input
  | opening => exact cap_open_program_termination oracle input.1 input.2
  | check => exact cap_check_termination oracle input

theorem cap_open_empty_succeeded
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    capProgram.openingSucceeded (capOpenEmptyResult trapdoor positions) = true := by
  have length : ((capOpenEmptyResult trapdoor positions).state.getReg .x11).toNat = 0 := by
    rw [show (capOpenEmptyResult trapdoor positions).state =
      capOpenExitState (capOpenInitializedState
        (capProgram.initialState .opening (trapdoor, positions))) by rfl,
      cap_open_empty_report]
    rfl
  simp only [Submission.openingSucceeded, length]
  rfl

theorem cap_open_support_success
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (opened : Execution)
    (reachable : opened ∈ support (capProgram.run .opening (trapdoor,positions))) :
    capProgram.openingSucceeded opened = true := by
  by_cases empty : positions.card = 0
  · rw [cap_open_empty_program_run trapdoor positions empty] at reachable
    simp only [support_pure,Set.mem_singleton_iff] at reachable
    subst opened
    exact cap_open_empty_succeeded trapdoor positions
  · have positive := Nat.pos_of_ne_zero empty
    rw [cap_open_nonempty_program_run trapdoor positions positive] at reachable
    simp only [support_pure,Set.mem_singleton_iff] at reachable
    subst opened
    exact cap_open_nonempty_succeeded trapdoor positions positive

private theorem honest_machine (program : Submission) (message : Message)
    (positions : Positions) :
    program.honestMachine message positions =
      (do let committed ← program.run .commit message
          let opened ← program.run .opening ((program.readCommit committed).2,positions)
          return ⟨committed.exit == Exit.success && program.openingSucceeded opened,
            committed.cycles,opened.cycles,(program.readProof opened).length⟩) := rfl

theorem cap_machine_support_success (message : Message) (positions : Positions)
    (result : MachineResult)
    (reachable : result ∈ support (capProgram.honestMachine message positions)) :
    result.success = true := by
  rw [honest_machine] at reachable
  simp only [mem_support_bind_iff] at reachable
  obtain ⟨committed,committedReached,opened,openedReached,returned⟩ := reachable
  rw [cap_commit_run_same] at committedReached
  have resources := commit_input_resources message committed committedReached
  have success := cap_open_support_success _ positions opened openedReached
  simp only [support_pure,Set.mem_singleton_iff] at returned
  subst result
  simp only [resources.1,beq_self_eq_true,Bool.true_and,success]

theorem cap_program_machine_success : capProgram.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact cap_machine_support_success message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)

theorem cap_machine_support_cycles (message : Message) (positions : Positions)
    (batch : positions.card = BATCH) (result : MachineResult)
    (reachable : result ∈ support (capProgram.honestMachine message positions)) :
    result.commitCycles ≤ 1728053684 ∧ result.openingCycles ≤ 43531 := by
  rw [honest_machine] at reachable
  simp only [mem_support_bind_iff] at reachable
  obtain ⟨committed,committedReached,opened,openedReached,returned⟩ := reachable
  rw [cap_commit_run_same] at committedReached
  have resources := commit_input_resources message committed committedReached
  have positive : 0 < positions.card := by rw [batch]; decide
  rw [cap_open_nonempty_program_run _ positions positive] at openedReached
  simp only [support_pure,Set.mem_singleton_iff] at openedReached returned
  subst opened
  subst result
  exact ⟨resources.2.1.le,
    cap_open_result_batch_cycles (capProgram.readCommit committed).2 positions batch⟩

theorem cap_program_prover_cycles : capProgram.ProverCycles 1728053684 43531 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact cap_machine_support_cycles message positions batch result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)

end CommitGolfCandidate
