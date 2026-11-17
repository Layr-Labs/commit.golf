import CommitGolfCandidate.OctParentLoop
import CommitGolfCandidate.QuadParentExit

/-! A first four-parent block aligns the residual for the eight-parent loop. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

def OctExitFetched (image : Image) : Prop :=
  ∀ state : MachineState,
    (state.pc = 4652 → fetch image state = some (.base (.JAL .x0 2096912))) ∧
    (state.pc = 4756 → fetch image state = some (.base (.JAL .x0 2096808)))

/-- Both physical exits target PC4412 without changing any caller register. -/
theorem oct_parent_exit (image : Image) (fetched : OctExitFetched image)
    (state : MachineState) (start : Word) (location : start = 4652 ∨ start = 4756)
    (fuel : Nat) :
    execute image (1 + fuel) (state.setPC start) true =
      (do let result ← execute image fuel (state.setPC 4412) true
          return result.charge 1 0) := by
  rcases location with rfl | rfl
  · have stepped : ordinaryStep (state.setPC 4652) (.base (.JAL .x0 2096912)) =
        some (state.setPC 4412) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
        MachineState.setReg, MachineState.setPC]
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
      ((fetched (state.setPC 4652)).1 rfl) stepped]
    rfl
  · have stepped : ordinaryStep (state.setPC 4756) (.base (.JAL .x0 2096808)) =
        some (state.setPC 4412) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
        MachineState.setReg, MachineState.setPC]
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
      ((fetched (state.setPC 4756)).2 rfl) stepped]
    rfl

/-- Run the positive group loop or the entry pair's zero-group exit directly. -/
theorem oct_group_remainder (image : Image)
    (sequenceFetched : ParentSequenceFetched image 4656 8)
    (branchFetched : OctBranchFetched image false) (exitFetched : OctExitFetched image)
    (state : MachineState) (groups : Nat) (bounded : 8 * groups < 2 ^ 24)
    (pointers : ParentPointerInvariant state (8 * groups))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (8 * groups)) (fuel : Nat) :
    execute image (25 * groups + 1 + fuel)
      (state.setPC (if groups = 0 then 4652 else 4656)) true =
      (do let finished ← commitParents state (8 * groups)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (81 * groups + 1) (8 * groups)) := by
  by_cases empty : groups = 0
  · subst groups
    simp only [Nat.mul_zero, Nat.zero_add, ite_true, commitParents, pure_bind]
    exact oct_parent_exit image exitFetched state 4652 (Or.inl rfl) fuel
  · have loop := oct_parents_loop image sequenceFetched branchFetched state groups
      bounded pointers constants buffers (1 + fuel)
    simp only [if_neg empty] at loop ⊢
    rw [show 25 * groups + 1 + fuel = 25 * groups + (1 + fuel) by omega, loop]
    apply bind_congr_of_forall_mem_support
    intro finished _
    rw [oct_parent_exit image exitFetched finished 4756 (Or.inr rfl) fuel]
    simp [Execution.charge, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- The retained four-parent block peels four parents before the eight-parent loop.
Its new branch targets the appended body instead of returning to the pair. -/
theorem oct_quad_remainder (image : Image)
    (firstFetched : ParentSequenceFetched image 4600 4)
    (entryBranch : OctBranchFetched image true)
    (sequenceFetched : ParentSequenceFetched image 4656 8)
    (branchFetched : OctBranchFetched image false) (exitFetched : OctExitFetched image)
    (state : MachineState) (groups : Nat) (bounded : 8 * groups + 4 < 2 ^ 24)
    (pointers : ParentPointerInvariant state (8 * groups + 4))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (8 * groups + 4)) (fuel : Nat) :
    execute image (25 * groups + 14 + fuel) (state.setPC 4600) true =
      (do let finished ← commitParents state (8 * groups + 4)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (81 * groups + 42) (8 * groups + 4)) := by
  rw [show 25 * groups + 14 + fuel = 13 + (25 * groups + 1 + fuel) by omega,
    oct_sequence_branch image 4600 4 true firstFetched entryBranch rfl state groups
      (by omega) pointers constants buffers]
  rw [show 8 * groups + 4 = 4 + 8 * groups by omega, parent_sequence_comp]
  simp only [bind_assoc, octBranchPC, ite_true]
  apply bind_congr_of_forall_mem_support
  intro middle reachable
  have invariants := parent_sequence_invariant state 4 (8 * groups)
    pointers constants buffers middle reachable
  change (do let result ← execute image (25 * groups + 1 + fuel)
               (middle.setPC (if groups = 0 then 4652 else 4656)) true
             return result.charge 41 4) = _
  rw [oct_group_remainder image sequenceFetched branchFetched exitFetched middle groups
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
