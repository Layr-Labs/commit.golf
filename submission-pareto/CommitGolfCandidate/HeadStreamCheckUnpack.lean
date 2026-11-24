import CommitGolfCandidate.HeadStreamCheckGuards

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec

theorem wf_records (k L : Nat) (wf : WellFormed k L) : 481*k≤L := by
  obtain ⟨_,_,many,eq⟩ := wf
  rw [eq]
  unfold packedLength bodyLength
  omega

theorem restored_steps_bound (input : CheckInput) (fits : input.proof.length≤8355061248) :
    entrySteps input.positions.card input.proof.length≤2^38 := by
  letI : UnpackOrigin := ⟨(headStart input).mem⟩
  have kb := TwoPermutationPrototype.Checker.checker_positions_bound input
  have tail := tail_steps_bound input fits
  have bound := restore_steps_bound input.positions.card (input.proof.length+input.positions.card/8+input.positions.card)
  unfold entrySteps
  omega

theorem converted_unpack (input : CheckInput) (fits : input.proof.length≤8355061248)
    (capacity : input.proof.length+input.positions.card/8+input.positions.card≤8355061248)
    (wf : WellFormed input.positions.card (input.proof.length+input.positions.card/8+input.positions.card)) :
    letI : UnpackOrigin := ⟨(headStart input).mem⟩
    ∃ t,Hop (Assembly.submission.initialState .check input) t
      (entrySteps input.positions.card input.proof.length+
        unpackSteps input.positions.card (input.proof.length+input.positions.card/8+input.positions.card))
      (entryCycles input.positions.card input.proof.length+
        unpackCycles input.positions.card (input.proof.length+input.positions.card/8+input.positions.card)) ∧
      UnpackedView (unpackInput (restoredInput input)) t := by
  letI : UnpackOrigin := ⟨(headStart input).mem⟩
  obtain ⟨t,hop,view⟩ := unpack_run (restoredInput input)
    (by simpa only [restored_length] using capacity)
    (by simpa only [restored_positions,restored_length] using wf)
  refine ⟨t,?_,view⟩
  have first := restored_entry input fits capacity (wf_records _ _ wf)
  simpa only [restored_positions,restored_length] using first.thenDo hop

theorem converted_reject (input : CheckInput) (fits : input.proof.length≤8355061248)
    (bad : ¬(input.proof.length+input.positions.card/8+input.positions.card≤8355061248 ∧
      WellFormed input.positions.card (input.proof.length+input.positions.card/8+input.positions.card))) :
    ∃ steps cycles t,steps≤2^38+27 ∧ ∀ fuel,
      execute packedImage (steps+3+fuel) (Assembly.submission.initialState .check input) false=
        pure ⟨.failure,headerRejectState t,cycles+3,0⟩ := by
  letI : UnpackOrigin := ⟨(headStart input).mem⟩
  by_cases capacity : input.proof.length+input.positions.card/8+input.positions.card≤8355061248
  · by_cases records : 481*input.positions.card ≤ input.proof.length+input.positions.card/8+input.positions.card
    · have malformed : ¬WellFormed input.positions.card (input.proof.length+input.positions.card/8+input.positions.card) := by tauto
      obtain ⟨steps,cycles,t,bound,ran⟩ := unpack_reject (restoredInput input)
        (by simpa only [restored_length] using capacity)
        (by simpa only [restored_positions,restored_length] using malformed)
      have first := restored_entry input fits capacity records
      refine ⟨entrySteps input.positions.card input.proof.length+steps,
        entryCycles input.positions.card input.proof.length+cycles,t,
        by have := restored_steps_bound input fits;omega,?_⟩
      intro fuel
      rw [show entrySteps input.positions.card input.proof.length+steps+3+fuel=
        (entrySteps input.positions.card input.proof.length)+(steps+3+fuel) by omega,
        first (steps+3+fuel),ran fuel]
      simp [Execution.charge,Nat.add_assoc]
    · obtain ⟨steps,cycles,t,bound,ran⟩ := entry_guard_reject input fits (Or.inr (by omega))
      exact ⟨steps,cycles,t,by omega,ran⟩
  · obtain ⟨steps,cycles,t,bound,ran⟩ := entry_guard_reject input fits (Or.inl (by omega))
    exact ⟨steps,cycles,t,by omega,ran⟩

end TwoPermutationPrototype.Packed.Checker.HeadRestore
