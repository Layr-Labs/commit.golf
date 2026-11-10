import CommitGolfCandidate.PointerParents

/-! Actual descending parent construction. Address setup occurs once; the loop
reads its two children through x10 and writes the parent through x12. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

abbrev commitParentQuery := pointerParentQuery
abbrev commitParentState := pointerParentState
abbrev commitParentNextState := pointerParentNextState

theorem commit_parent_written_memory (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).mem =
      (writeBits state (state.getReg .x12) answer).mem := rfl

theorem commit_parent_pc (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).pc = state.pc + 4 := by
  simp [pointerParentState, writeBits, MachineState.setPC]

theorem commit_parent_register (state : MachineState) (answer : BitVec 256) (reg : Reg) :
    (commitParentState state answer).getReg reg = state.getReg reg :=
  pointer_parent_register state answer reg

theorem commit_parent_step_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (member : reg ∈ [Reg.x9, .x19, .x20, .x21, .x26, .x5, .x11, .x13]) :
    (commitParentNextState (commitParentState state answer)).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [pointerParentNextState, pointerParentAdvance, pointer_parent_register,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem commit_parent_step_input (state : MachineState) (answer : BitVec 256) :
    (commitParentNextState (commitParentState state answer)).getReg .x10 =
      state.getReg .x10 - 64 := by
  simp [pointerParentNextState, pointerParentAdvance, pointer_parent_register,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem commit_parent_step_output (state : MachineState) (answer : BitVec 256) :
    (commitParentNextState (commitParentState state answer)).getReg .x12 =
      state.getReg .x12 - 32 := by
  simp [pointerParentNextState, pointerParentAdvance, pointer_parent_register,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem commit_parent_step_pc (state : MachineState) (answer : BitVec 256) :
    (commitParentNextState (commitParentState state answer)).pc =
      if state.getReg .x12 - 32 = state.getReg .x9 then 4404 else 4388 := by
  simp [pointerParentNextState, pointer_parent_register, MachineState.setPC]

/-- One parent costs four instructions, eleven cycles and one query. The final
terminal jump is charged once by the whole-tree execution theorem. -/
theorem commit_parent (state : MachineState) (pc : state.pc = 4388)
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 64 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0) (fuel : Nat) :
    execute (submission.image .commit) (4 + fuel) state true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute (submission.image .commit) fuel
            (commitParentNextState (commitParentState state answer)) true
          return result.charge 11 1) := by
  rw [show 4 + fuel = 1 + (3 + fuel) by omega,
    pointer_parent_compression state pc constants sourceValid destinationValid sourceAligned destinationAligned]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (commitParentQuery state))) : OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have nextPC : (commitParentState state answer).pc = 4392 := by rw [commit_parent_pc, pc]; rfl
  rw [pointer_parent_next _ nextPC]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
