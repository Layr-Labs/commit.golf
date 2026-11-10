import CommitGolfCandidate.OuterFrame
/-! The real heap-end branch controls leaf execution. Virtual x20 is used only
by the reference refinement, then erased before the parent setup overwrites it. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Three fetched ordinary instructions advance both pointers and branch on heap end. -/
theorem heap_latch_execute (state : MachineState) (pc : state.pc=4348) (fuel : Nat) :
    execute (submission.image .commit) (3+fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (outerPhysicalNextState state) true
          return result.charge 3 0) := by
  apply outer_latch_execute _ state fuel pc
  intro i hi
  apply commit_fetch _ (63+i) _ (by omega)
  · interval_cases i <;> simp [outerLatchPrefix,outerLatchInstructions,execInstrBr,pc,MachineState.setPC]
  · interval_cases i <;> rfl

/-- No physical counter is incremented. The old reference increment is normalized away. -/
theorem heap_latch_normalized (state : MachineState) (counter : state.getReg .x20=0) :
    outerPhysicalNextState state =
      outerNormalize (commitPositionNextState state)
        (if BitVec.ult (state.getReg .x23+32) (state.getReg .x22) then 4280 else 4360) := by
  cases state
  dsimp [outerPhysicalNextState,outerNormalize,commitPositionNextState,MachineState.getReg,
    MachineState.setReg,MachineState.setPC] at counter ⊢
  congr 1
  funext reg
  cases reg <;> simp_all

/-- Normalization changes only the reference counter and program counter. -/
theorem heap_normalize_register (state : MachineState) (pc : Word) (reg : Reg)
    (notCounter : reg ≠ .x20) :
    (outerNormalize state pc).getReg reg=state.getReg reg := by
  simp only [outerNormalize,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCounter)]

/-- At the ABI entry the physical counter is already zero. -/
theorem heap_normalize_state (state : MachineState) (pc : Word)
    (counter : state.getReg .x20=0) :
    outerNormalize state pc=state.setPC pc := by
  cases state
  dsimp [outerNormalize,MachineState.getReg,MachineState.setReg,MachineState.setPC] at counter ⊢
  congr 1
  funext reg
  cases reg <;> simp_all

attribute [local irreducible] execute commitPositionRun

/-- The exit-only NOP is paid once and restores the retained parent entry PC. -/
theorem heap_latch_exit (state : MachineState) (pc : state.pc=4360) (fuel : Nat) :
    execute (submission.image .commit) (1+fuel) state true =
      (do let result ← execute (submission.image .commit) fuel
            (execInstrBr state (.ADDI .x0 .x0 0)) true
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state=some (.base (.ADDI .x0 .x0 0)) := by
    apply commit_fetch _ 66 _ (by decide) pc; rfl
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched (by rfl)]
  rfl

/-- Exit padding and parent initialization erase the physical counter frame.
The NOP costs one and the positive parent setup costs six, exactly once. -/
theorem heap_latch_parent_setup (state : MachineState) (pc : state.pc=4364)
    (nonempty : state.getReg .x19-1 ≠ 0) (fuel : Nat) :
    execute (submission.image .commit) (7+fuel) (outerNormalize state 4360) true =
      (do let result ← execute (submission.image .commit) fuel (commitParentsStartState state) true
          return result.charge 7 0) := by
  let afterNop := execInstrBr (outerNormalize state 4360) (.ADDI .x0 .x0 0)
  have nextPC : afterNop.pc=4364 := rfl
  have nextCount : afterNop.getReg .x19=state.getReg .x19 := rfl
  rw [show 7+fuel=1+(6+fuel) by omega,heap_latch_exit _ rfl,
    commit_parents_start afterNop nextPC (by rw [nextCount]; exact nonempty)]
  rw [outer_exit_parent_frame]
  rw [← pc,hoist_pc_self]
  simp [Execution.charge,← Nat.add_assoc]

end CommitGolfCandidate
