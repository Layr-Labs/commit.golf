import CommitGolfCandidate.QuadParentLoop
import CommitGolfCandidate.FusedParentExit

/-! The first pair falls through at PC4344 when no four-parent group remains.
A positive four-parent loop falls through at PC4652. Each path pays one JAL
to the unchanged root-copy entry; neither jump belongs to the loop body. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

def QuadExitFetched (image : Image) : Prop :=
  ∀ state : MachineState,
    (state.pc = 4344 → fetch image state = some (.base (.JAL .x0 68))) ∧
    (state.pc = 4652 → fetch image state = some (.base (.JAL .x0 2096912)))

/-- Both physical exits target PC4412 without changing any caller register. -/
theorem quad_parent_exit (image : Image) (fetched : QuadExitFetched image)
    (state : MachineState) (start : Word) (location : start = 4344 ∨ start = 4652)
    (fuel : Nat) :
    execute image (1 + fuel) (state.setPC start) true =
      (do let result ← execute image fuel (state.setPC 4412) true
          return result.charge 1 0) := by
  rcases location with rfl | rfl
  · have stepped : ordinaryStep (state.setPC 4344) (.base (.JAL .x0 68)) =
        some (state.setPC 4412) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
        MachineState.setReg, MachineState.setPC]
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
      ((fetched (state.setPC 4344)).1 rfl) stepped]
    rfl
  · have stepped : ordinaryStep (state.setPC 4652) (.base (.JAL .x0 2096912)) =
        some (state.setPC 4412) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
        MachineState.setReg, MachineState.setPC]
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
      ((fetched (state.setPC 4652)).2 rfl) stepped]
    rfl

/-- Run the positive group loop or the entry pair's zero-group exit directly. -/
theorem quad_group_remainder (image : Image)
    (sequenceFetched : ParentSequenceFetched image 4600 4)
    (branchFetched : QuadBranchFetched image false) (exitFetched : QuadExitFetched image)
    (state : MachineState) (groups : Nat) (bounded : 4 * groups < 2 ^ 24)
    (pointers : ParentPointerInvariant state (4 * groups))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (4 * groups)) (fuel : Nat) :
    execute image (13 * groups + 1 + fuel)
      (state.setPC (if groups = 0 then 4344 else 4600)) true =
      (do let finished ← commitParents state (4 * groups)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (41 * groups + 1) (4 * groups)) := by
  by_cases empty : groups = 0
  · subst groups
    simp only [Nat.mul_zero, Nat.zero_add, ite_true, commitParents, pure_bind]
    exact quad_parent_exit image exitFetched state 4344 (Or.inl rfl) fuel
  · have loop := quad_parents_loop image sequenceFetched branchFetched state groups
      bounded pointers constants buffers (1 + fuel)
    simp only [if_neg empty] at loop ⊢
    rw [show 13 * groups + 1 + fuel = 13 * groups + (1 + fuel) by omega, loop]
    apply bind_congr_of_forall_mem_support
    intro finished _
    rw [quad_parent_exit image exitFetched finished 4652 (Or.inr rfl) fuel]
    simp [Execution.charge, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- The retained first pair peels two parents before the appended group loop.
Its new branch targets the appended body instead of returning to the pair. -/
theorem quad_pair_remainder (image : Image)
    (pairFetched : ParentSequenceFetched image 4316 2)
    (entryBranch : QuadBranchFetched image true)
    (sequenceFetched : ParentSequenceFetched image 4600 4)
    (branchFetched : QuadBranchFetched image false) (exitFetched : QuadExitFetched image)
    (state : MachineState) (groups : Nat) (bounded : 4 * groups + 2 < 2 ^ 24)
    (pointers : ParentPointerInvariant state (4 * groups + 2))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (4 * groups + 2)) (fuel : Nat) :
    execute image (13 * groups + 8 + fuel) (state.setPC 4316) true =
      (do let finished ← commitParents state (4 * groups + 2)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (41 * groups + 22) (4 * groups + 2)) := by
  rw [show 13 * groups + 8 + fuel = 7 + (13 * groups + 1 + fuel) by omega,
    parent_sequence_branch image 4316 2 true pairFetched entryBranch rfl state groups
      (by omega) pointers constants buffers]
  rw [show 4 * groups + 2 = 2 + 4 * groups by omega, parent_sequence_comp]
  simp only [bind_assoc, quadBranchPC, ite_true]
  apply bind_congr_of_forall_mem_support
  intro middle reachable
  have invariants := parent_sequence_invariant state 2 (4 * groups)
    pointers constants buffers middle reachable
  change (do let result ← execute image (13 * groups + 1 + fuel)
               (middle.setPC (if groups = 0 then 4344 else 4600)) true
             return result.charge 21 2) = _
  rw [quad_group_remainder image sequenceFetched branchFetched exitFetched middle groups
    (by omega) invariants.1 invariants.2.1 invariants.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished _
  apply congrArg (fun continuation =>
    execute image fuel (finished.setPC 4412) true >>= continuation)
  funext result
  congr 1
  cases result
  simp only [Execution.charge]
  congr 1 <;> omega

end CommitGolfCandidate
