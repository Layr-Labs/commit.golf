import CommitGolfCandidate.NonceOpeningResources
import CommitGolfCandidate.CapCommitBridge
import CommitGolfCandidate.Machine

/-! Machine success and scored prover cycles for the concrete codec images.
Commitment execution is unchanged; every actual opening succeeds and its
complete additional work is included in the 172309-cycle batch bound. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_commit_run_same (message : Message) :
    nonceCompressedProgram.run .commit message=submission.run .commit message := rfl

theorem nonce_open_support_success
    (trapdoor : BitVec (8*nonceCompressedProgram.sizes.trapdoor)) (positions : Positions)
    (opened : Execution)
    (reachable : opened ∈ support (nonceCompressedProgram.run .opening (trapdoor,positions))) :
    nonceCompressedProgram.openingSucceeded opened=true := by
  erw [nonce_compressed_opening_run] at reachable
  simp only [support_pure,Set.mem_singleton_iff] at reachable
  subst opened
  exact nonce_compressed_result_succeeded trapdoor positions

private theorem honest_machine (program : Submission) (message : Message)
    (positions : Positions) :
    program.honestMachine message positions =
      (do let committed ← program.run .commit message
          let opened ← program.run .opening ((program.readCommit committed).2,positions)
          return ⟨committed.exit == Exit.success && program.openingSucceeded opened,
            committed.cycles,opened.cycles,(program.readProof opened).length⟩) := rfl

theorem nonce_machine_support_success (message : Message) (positions : Positions)
    (result : MachineResult)
    (reachable : result ∈ support (nonceCompressedProgram.honestMachine message positions)) :
    result.success = true := by
  rw [honest_machine] at reachable
  simp only [mem_support_bind_iff] at reachable
  obtain ⟨committed,committedReached,opened,openedReached,returned⟩ := reachable
  rw [nonce_commit_run_same] at committedReached
  have resources := commit_input_resources message committed committedReached
  have success := nonce_open_support_success _ positions opened openedReached
  simp only [support_pure,Set.mem_singleton_iff] at returned
  subst result
  simp only [resources.1,beq_self_eq_true,Bool.true_and,success]

theorem nonce_program_machine_success : nonceCompressedProgram.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact nonce_machine_support_success message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)

theorem nonce_machine_support_cycles (message : Message) (positions : Positions)
    (batch : positions.card = BATCH) (result : MachineResult)
    (reachable : result ∈ support (nonceCompressedProgram.honestMachine message positions)) :
    result.commitCycles ≤ 520444244 ∧ result.openingCycles ≤ 172309 := by
  rw [honest_machine] at reachable
  simp only [mem_support_bind_iff] at reachable
  obtain ⟨committed,committedReached,opened,openedReached,returned⟩ := reachable
  rw [nonce_commit_run_same] at committedReached
  have resources := commit_input_resources message committed committedReached
  erw [nonce_compressed_opening_run] at openedReached
  simp only [support_pure,Set.mem_singleton_iff] at openedReached returned
  subst opened
  subst result
  exact ⟨resources.2.1.le,
    nonce_compressed_batch_cycles (nonceCompressedProgram.readCommit committed).2 positions batch⟩

theorem nonce_program_prover_cycles : nonceCompressedProgram.ProverCycles 520444244 172309 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact nonce_machine_support_cycles message positions batch result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)

end CommitGolfCandidate
