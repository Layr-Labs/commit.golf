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
    2+restoreSteps input.positions.card (input.proof.length+3*input.positions.card/8)≤2^37 := by
  have kb := TwoPermutationPrototype.Checker.checker_positions_bound input
  have bound := restore_steps_bound input.positions.card (input.proof.length+3*input.positions.card/8)
  omega

theorem converted_unpack (input : CheckInput) (fits : input.proof.length≤8355061248)
    (capacity : input.proof.length+3*input.positions.card/8≤8355061248)
    (wf : WellFormed input.positions.card (input.proof.length+3*input.positions.card/8)) :
    letI : UnpackOrigin := ⟨(headStart input).mem⟩
    ∃ t,Hop (Assembly.submission.initialState .check input) t
      (2+restoreSteps input.positions.card (input.proof.length+3*input.positions.card/8)+
        unpackSteps input.positions.card (input.proof.length+3*input.positions.card/8))
      (2+restoreCycles input.positions.card (input.proof.length+3*input.positions.card/8)+
        unpackCycles input.positions.card (input.proof.length+3*input.positions.card/8)) ∧
      UnpackedView (unpackInput (restoredInput input)) t := by
  letI : UnpackOrigin := ⟨(headStart input).mem⟩
  obtain ⟨t,hop,view⟩ := unpack_run (restoredInput input)
    (by simpa only [restored_length] using capacity)
    (by simpa only [restored_positions,restored_length] using wf)
  refine ⟨t,?_,view⟩
  have first := restored_entry input fits capacity (wf_records _ _ wf)
  simpa only [restored_positions,restored_length] using first.thenDo hop

theorem converted_reject (input : CheckInput) (fits : input.proof.length≤8355061248)
    (bad : ¬(input.proof.length+3*input.positions.card/8≤8355061248 ∧
      WellFormed input.positions.card (input.proof.length+3*input.positions.card/8))) :
    ∃ steps cycles t,steps≤2^37+27 ∧ ∀ fuel,
      execute packedImage (steps+3+fuel) (Assembly.submission.initialState .check input) false=
        pure ⟨.failure,headerRejectState t,cycles+3,0⟩ := by
  letI : UnpackOrigin := ⟨(headStart input).mem⟩
  by_cases capacity : input.proof.length+3*input.positions.card/8≤8355061248
  · by_cases records : 481*input.positions.card ≤ input.proof.length+3*input.positions.card/8
    · have malformed : ¬WellFormed input.positions.card (input.proof.length+3*input.positions.card/8) := by tauto
      obtain ⟨steps,cycles,t,bound,ran⟩ := unpack_reject (restoredInput input)
        (by simpa only [restored_length] using capacity)
        (by simpa only [restored_positions,restored_length] using malformed)
      have first := restored_entry input fits capacity records
      refine ⟨2+restoreSteps input.positions.card (input.proof.length+3*input.positions.card/8)+steps,
        2+restoreCycles input.positions.card (input.proof.length+3*input.positions.card/8)+cycles,t,
        by have := restored_steps_bound input fits;omega,?_⟩
      intro fuel
      rw [show 2+restoreSteps input.positions.card (input.proof.length+3*input.positions.card/8)+steps+3+fuel=
        (2+restoreSteps input.positions.card (input.proof.length+3*input.positions.card/8))+(steps+3+fuel) by omega,
        first (steps+3+fuel),ran fuel]
      simp [Execution.charge,Nat.add_assoc]
    · obtain ⟨steps,cycles,t,bound,ran⟩ := entry_guard_reject input fits (Or.inr (by omega))
      exact ⟨steps,cycles,t,by omega,ran⟩
  · obtain ⟨steps,cycles,t,bound,ran⟩ := entry_guard_reject input fits (Or.inl (by omega))
    exact ⟨steps,cycles,t,by omega,ran⟩

end TwoPermutationPrototype.Packed.Checker.HeadRestore
