import CommitGolfCandidate.NonceOldOpeningInputs

/-! Instantiate codec buffer admission with the retained opener's ABI result.
Empty openings have no footer; nonempty ones retain the exact traversal
boundary count already proved for the machine output. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
attribute [local irreducible] capOpenFinalState capOpenTraversalInitial capOpenRecordsFinal
  capOpenInitializedState capOpenEmptyResult capOpenNonemptyResult

def nonceOldFooterWords (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : Nat :=
  if positions.card=0 then 0 else 4*(capOpenBoundaryDigests trapdoor positions).length

private theorem exit_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x10 ∧ reg ≠ .x5 ∧ reg ≠ .x11) :
    (capOpenExitState state).getReg reg=state.getReg reg := by
  simp only [capOpenExitState, capOpenLengthState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2)]

theorem nonce_old_opening_ready (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    let state := (nonceOldOpeningResult trapdoor positions).state
    state.getReg .x15=BitVec.ofNat 64 capProgram.layout.proof ∧
    state.getReg .x16=BitVec.ofNat 64 positions.card ∧
    state.getReg .x25=BitVec.ofNat 64 (capProgram.layout.proof+544*positions.card+
      8*nonceOldFooterWords trapdoor positions) := by
  by_cases empty : positions.card=0
  · have resultEq : nonceOldOpeningResult trapdoor positions=capOpenEmptyResult trapdoor positions := by
      unfold nonceOldOpeningResult
      exact if_pos empty
    have endEq : capProgram.layout.proof+544*positions.card+
        8*nonceOldFooterWords trapdoor positions=capProgram.layout.proof := by
      unfold nonceOldFooterWords
      rw [if_pos empty,empty]
      rfl
    rw [resultEq,endEq]
    unfold capOpenEmptyResult
    have setup:=cap_open_setup_registers (capProgram.initialState .opening (trapdoor,positions))
    refine ⟨?_,?_,?_⟩
    · exact (exit_register _ .x15 (by decide)).trans setup.2.2.2.2.2.2.2.2.2.1
    · exact (exit_register _ .x16 (by decide)).trans setup.2.2.2.2.2.2.2.2.2.2
    · exact (exit_register _ .x25 (by decide)).trans setup.2.2.1
  · have resultEq : nonceOldOpeningResult trapdoor positions=capOpenNonemptyResult trapdoor positions := by
      unfold nonceOldOpeningResult
      exact if_neg empty
    have words : 8*nonceOldFooterWords trapdoor positions=
        32*(capOpenBoundaryDigests trapdoor positions).length := by
      unfold nonceOldFooterWords
      rw [if_neg empty]
      omega
    rw [resultEq,words]
    exact ⟨nonce_old_nonempty_base trapdoor positions,nonce_old_nonempty_count trapdoor positions,
      nonce_old_nonempty_end trapdoor positions (by omega)⟩

theorem nonce_old_footer_bound (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : nonceOldFooterWords trapdoor positions ≤ 4088 := by
  have boundaries:=cap_control_boundaries_length (capOpenRequestedMarks positions) 1022 (.visit 1)
  simp only [nonceOldFooterWords]
  split
  · omega
  · simp only [capOpenBoundaryDigests, List.length_map]
    omega

theorem nonce_old_codec_window (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    capProgram.layout.proof+544*positions.card+8*nonceOldFooterWords trapdoor positions ≤ MEMORY_BYTES := by
  have space:=cap_open_abi_output_space positions
  have footer:=nonce_old_footer_bound trapdoor positions
  omega

theorem nonce_old_count_bound (positions : Positions) : positions.card<2^64 := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  norm_num [LENGTH, LOG_LENGTH] at cardinal
  omega

theorem nonce_old_proof_aligned : capProgram.layout.proof%8=0 := by decide

end CommitGolfCandidate
