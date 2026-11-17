import CommitGolfCandidate.PointerTree

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def parentStartInstructions : List Instr :=
  [.ADDI .x20 .x19 4095, .SLLI .x6 .x20 6,
   .ADD .x10 .x9 .x6, .SLLI .x7 .x20 5]

private def parentStartPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentStartInstructions.take count).foldl execInstrBr state

private def parentStartBranchState (state : MachineState) : MachineState :=
  (parentStartPrefix state 4).setPC
    (if state.getReg .x19 - 1 = 0 then 4412 else 4384)

def commitParentsStartState (state : MachineState) : MachineState :=
  if state.getReg .x19 - 1 = 0 then parentStartBranchState state
  else execInstrBr (parentStartBranchState state) (.ADD .x12 .x9 .x7)

theorem commit_parents_start_register (state : MachineState) (reg : Reg)
    (member : reg ∈ [Reg.x9, .x19, .x21, .x26, .x5, .x11, .x13]) :
    (commitParentsStartState state).getReg reg = state.getReg reg := by
  unfold commitParentsStartState
  split <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem commit_parents_start_counter (state : MachineState) :
    (commitParentsStartState state).getReg .x20 = state.getReg .x19 - 1 := by
  unfold commitParentsStartState
  split <;> change state.getReg .x19 + 18446744073709551615 = state.getReg .x19 - 1
  all_goals simp [BitVec.sub_eq_add_neg]

theorem commit_parents_start_memory (state : MachineState) :
    (commitParentsStartState state).mem = state.mem := by
  unfold commitParentsStartState
  split <;> rfl

theorem commit_parents_start_constants (state : MachineState)
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0) :
    (commitParentsStartState state).getReg .x5 = 0 ∧
    (commitParentsStartState state).getReg .x11 = 64 ∧
    (commitParentsStartState state).getReg .x13 = 0 := by
  rw [commit_parents_start_register state .x5 (by simp),
    commit_parents_start_register state .x11 (by simp),
    commit_parents_start_register state .x13 (by simp)]
  exact constants

theorem commit_parents_start_pc (state : MachineState)
    (nonempty : state.getReg .x19 - 1 ≠ 0) :
    (commitParentsStartState state).pc = 4388 := by
  unfold commitParentsStartState
  rw [if_neg nonempty]
  change (if state.getReg .x19 - 1 = 0 then (4412 : Word) else 4384) + 4 = 4388
  rw [if_neg nonempty]
  rfl

set_option maxRecDepth 4096 in
theorem commit_parents_start_pointers (state : MachineState) (remaining : Nat)
    (nonempty : state.getReg .x19 - 1 ≠ 0)
    (counter : state.getReg .x19 - 1 = BitVec.ofNat 64 remaining) :
    ParentPointerInvariant (commitParentsStartState state) remaining := by
  unfold ParentPointerInvariant
  rw [commit_parents_start_register state .x9 (by simp)]
  unfold commitParentsStartState
  rw [if_neg nonempty]
  change (state.getReg .x9 + ((state.getReg .x19 + 18446744073709551615) <<< 6) =
      state.getReg .x9 + BitVec.ofNat 64 (64*remaining)) ∧
    (state.getReg .x9 + ((state.getReg .x19 + 18446744073709551615) <<< 5) =
      state.getReg .x9 + BitVec.ofNat 64 (32*remaining))
  have addCounter : state.getReg .x19 + 18446744073709551615 = BitVec.ofNat 64 remaining := by
    simpa [BitVec.sub_eq_add_neg] using counter
  rw [addCounter, parent_pointer_shift, parent_pointer_shift]
  exact ⟨rfl, rfl⟩

theorem commit_parents_start_pointers_of_count (state : MachineState) (count : Nat)
    (total : state.getReg .x19 = BitVec.ofNat 64 count)
    (positive : 2 ≤ count) (bounded : count ≤ 2^24) :
    ParentPointerInvariant (commitParentsStartState state) (count-1) := by
  have residual : state.getReg .x19 - 1 = BitVec.ofNat 64 (count-1) := by
    rw [total]
    change BitVec.ofNat 64 count - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) count 1 (by decide) (by omega)]
  have nonempty : state.getReg .x19 - 1 ≠ 0 := by
    rw [residual]
    intro zero
    have equal := congrArg BitVec.toNat zero
    change (count-1) % 18446744073709551616 = 0 at equal
    omega
  exact commit_parents_start_pointers state (count-1) nonempty residual

private theorem parent_start_branch (state : MachineState) (pc : state.pc = 4364) (fuel : Nat) :
    execute (submission.image .commit) (5 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (parentStartBranchState state) true
          return result.charge 5 0) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (4 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (parentStartPrefix state 4) true
            return result.charge 4 0) := by
    apply execute_unit_steps (states := parentStartPrefix state)
    intro i hi
    refine ⟨.base ((parentStartInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (67 + i) _ (by omega)
      · interval_cases i <;> simp [parentStartPrefix, parentStartInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let next := parentStartPrefix state 4
  have fetched : fetch (submission.image .commit) next = some (.base (.BEQ .x20 .x0 32)) := by
    apply commit_fetch _ 71 _ (by decide)
    · simp [next, parentStartPrefix, parentStartInstructions, execInstrBr, pc, MachineState.setPC]
    · rfl
  have stepped : ordinaryStep next (.base (.BEQ .x20 .x0 32)) = some (parentStartBranchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, parentStartBranchState, parentStartPrefix, parentStartInstructions,
      signExtend12, pc, MachineState.getReg, MachineState.setReg, MachineState.setPC,
      BitVec.sub_eq_add_neg]
    split <;> simp_all
  rw [show 5 + fuel = 4 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

theorem commit_parents_start (state : MachineState) (pc : state.pc = 4364)
    (nonempty : state.getReg .x19 - 1 ≠ 0) (fuel : Nat) :
    execute (submission.image .commit) (6 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitParentsStartState state) true
          return result.charge 6 0) := by
  let next := parentStartBranchState state
  have fetched : fetch (submission.image .commit) next = some (.base (.ADD .x12 .x9 .x7)) := by
    apply commit_fetch _ 72 _ (by decide)
    · simp only [next, parentStartBranchState, if_neg nonempty, MachineState.setPC]
      rfl
    · rfl
  have stepped : ordinaryStep next (.base (.ADD .x12 .x9 .x7)) = some (commitParentsStartState state) := by
    simp only [commitParentsStartState, if_neg nonempty]
    simp [ordinaryStep, memoryArgumentsValid, memAccess, next]
  rw [show 6 + fuel = 5 + (1 + fuel) by omega, parent_start_branch state pc,
    show 1 + fuel = fuel + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

theorem commit_parents_start_empty (state : MachineState) (pc : state.pc = 4364)
    (empty : state.getReg .x19 - 1 = 0) (fuel : Nat) :
    execute (submission.image .commit) (5 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitParentsStartState state) true
          return result.charge 5 0) := by
  simpa only [commitParentsStartState, if_pos empty] using parent_start_branch state pc fuel

end CommitGolfCandidate
