import CommitGolfCandidate.FusedTree

/-! Pure reference preparation erases an incoming return link and PC. The real
contiguous loop sets x1 once at entry; a positive reference leaf head overwrites
that same link. Zero-leaf state equality is deliberately not asserted. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem contiguous_position_state (state : MachineState) (link pc : Word) :
    commitPositionState ((state.setReg .x1 link).setPC pc) = commitPositionState state := by
  unfold commitPositionState commitLeafCallState
  rw [commit_copy_expansion, commit_copy_expansion]
  cases state
  dsimp [List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.getMem, MachineState.setMem, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem contiguous_position_run (state : MachineState) (link pc : Word) :
    commitPositionRun ((state.setReg .x1 link).setPC pc) = commitPositionRun state := by
  simp only [commitPositionRun, contiguous_position_state]

theorem contiguous_positive_leaves (state : MachineState) (remaining : Nat) (link pc : Word) :
    commitLeaves ((state.setReg .x1 link).setPC pc) (remaining + 1) =
      commitLeaves state (remaining + 1) := by
  simp only [commitLeaves, contiguous_position_run]

/-- Each reference leaf explicitly selects the same fixed return link. -/
theorem contiguous_position_link (state finished : MachineState)
    (reached : finished ∈ support (commitPositionRun state)) :
    finished.getReg .x1 = 4316 := by
  simp only [commitPositionRun, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at reached
  obtain ⟨leaf, member, rfl⟩ := reached
  have preserved := (commit_leaf_loop_registers
    (commitLeafReadyState (commitPositionState state)) 8 leaf member).2 .x1 (by decide)
  change leaf.getReg .x1 = _
  rw [preserved, commit_leaf_ready_register]
  rfl

end CommitGolfCandidate
