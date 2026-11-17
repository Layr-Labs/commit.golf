import CommitGolfCandidate.Compact.SlimInput

/-! The actual unrolled machine returns exactly the reference proof bytes for
all trapdoors and position sets. Thus its machine-derived scheme is equal to the
already certified scheme, allowing completeness and security to transfer. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem slim_result_exit_frame (s : MachineState) (pc : Word) :
    slimExitState (s.setPC pc)=slimExitState s := rfl

/-- The final program counter is the only state difference. -/
theorem slim_result_state (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) :
    (slimOpeningResult trapdoor positions).state=
      (openingResult trapdoor positions).state.setPC 5524 := by
  let initial := submission.initialState .opening (trapdoor,positions)
  by_cases empty : positions.card=0
  · simp only [slimOpeningResult,openingResult,empty,Function.iterate_zero,id_eq]
    rw [slim_result_exit_frame]
    unfold slimInitializedState
    rw [slim_result_exit_frame]
    rfl
  · have cardinal : positions.card≤LENGTH := by
      simpa [Index] using Finset.card_le_univ positions
    have nonzero : initial.getReg .x16≠0 := by
      change BitVec.ofNat 64 positions.card≠(0 : Word)
      intro zero
      have equal := congrArg BitVec.toNat zero
      change positions.card%2^64=0 at equal
      rw [Nat.mod_eq_of_lt (by norm_num [LENGTH,LOG_LENGTH] at cardinal;omega)] at equal
      omega
    have oldPC : (openingInitializedState initial).pc=4176 := by
      change (if initial.getReg .x16=0 then 4320 else 4176)=4176
      rw [if_neg nonzero]
    have ready : slimInitializedState initial=openingInitializedState initial := by
      unfold slimInitializedState
      rw [if_neg nonzero,←oldPC]
      generalize openingInitializedState initial=s
      cases s
      rfl
    simp only [slimOpeningResult,openingResult]
    rw [ready,slim_result_exit_frame]
    rfl

theorem slim_result_succeeded (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) :
    slimSubmission.openingSucceeded (slimOpeningResult trapdoor positions)=true := by
  unfold Submission.openingSucceeded
  rw [slim_result_state]
  exact opening_result_succeeded trapdoor positions

/-- This equality includes the success/capacity checks and the transmitted byte list. -/
theorem slim_read_proof (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) :
    slimSubmission.readProof (slimOpeningResult trapdoor positions)=
      submission.readProof (openingResult trapdoor positions) := by
  simp only [Submission.readProof,slim_result_succeeded,opening_result_succeeded,ite_true]
  rw [slim_result_state]
  rfl

/-- The commitment and checker are identical; the opening equality follows from
complete execution of the new image and equality of every returned proof byte. -/
theorem slim_scheme_eq : slimSubmission.scheme=submission.scheme := by
  unfold Submission.scheme
  congr 1
  funext trapdoor positions
  change (slimSubmission.readProof <$> slimSubmission.run .opening (trapdoor,positions))=
    (submission.readProof <$> submission.run .opening (trapdoor,positions))
  rw [slim_opening_execution trapdoor positions,opening_execution trapdoor positions]
  simp only [map_pure]
  exact congrArg (fun proof : Proof => (pure proof : OracleComp World Proof))
    (slim_read_proof trapdoor positions)
end CommitGolfCandidate.Compact
