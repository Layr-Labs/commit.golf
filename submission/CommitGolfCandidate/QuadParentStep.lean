import CommitGolfCandidate.ParentSequence

/-! The entry pair and the four-parent body share the same residual test.
Their physical branch PCs and fall-through exits differ, so both remain explicit
in the operational bridge rather than being hidden in a reference-state frame. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

def quadBranchPC (entry : Bool) : Word := if entry then 4340 else 4648

def QuadBranchFetched (image : Image) (entry : Bool) : Prop :=
  ∀ state : MachineState,
    state.pc = quadBranchPC entry →
      fetch image state = some (.base (.BNE .x12 .x9 (if entry then 260 else 8144)))

/-- The branch tests the actual decremented output pointer. A nonzero residual
enters the appended body at PC4600; zero falls through at the branch's own PC. -/
theorem quad_branch (image : Image) (entry : Bool)
    (fetched : QuadBranchFetched image entry) (state : MachineState) (groups : Nat)
    (bounded : 4 * groups < 2 ^ 24)
    (pointers : ParentPointerInvariant state (4 * groups)) (fuel : Nat) :
    execute image (1 + fuel) (state.setPC (quadBranchPC entry)) true =
      (do let result ← execute image fuel
            (state.setPC (if groups = 0 then quadBranchPC entry + 4 else 4600)) true
          return result.charge 1 0) := by
  have done : state.getReg .x12 = state.getReg .x9 ↔ groups = 0 := by
    rw [pointers.2, parent_pointer_done_iff _ (4 * groups) bounded]
    omega
  change state.regs .x12 = state.regs .x9 ↔ groups = 0 at done
  have stepped : ordinaryStep (state.setPC (quadBranchPC entry))
      (.base (.BNE .x12 .x9 (if entry then 260 else 8144))) =
      some (state.setPC (if groups = 0 then quadBranchPC entry + 4 else 4600)) := by
    cases entry <;>
      simp [quadBranchPC, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
        signExtend13, MachineState.getReg, MachineState.getReg_setPC,
        MachineState.setPC, done] <;>
      split <;> simp_all
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
    (fetched (state.setPC (quadBranchPC entry)) rfl) stepped]
  rfl

/-- Compose any fetched unrolled prefix with its real end-pointer branch.
The entry pair uses count two; the repeated body uses count four. -/
theorem parent_sequence_branch (image : Image) (start : Word) (count : Nat)
    (entry : Bool) (sequenceFetched : ParentSequenceFetched image start count)
    (branchFetched : QuadBranchFetched image entry)
    (endPC : parentSequenceEnd start count = quadBranchPC entry)
    (state : MachineState) (groups : Nat) (bounded : 4 * groups < 2 ^ 24)
    (pointers : ParentPointerInvariant state (4 * groups + count))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (4 * groups + count)) (fuel : Nat) :
    execute image (3 * count + 1 + fuel) (state.setPC start) true =
      (do let finished ← commitParents state count
          let result ← execute image fuel
            (finished.setPC (if groups = 0 then quadBranchPC entry + 4 else 4600)) true
          return result.charge (10 * count + 1) count) := by
  rw [show 3 * count + 1 + fuel = 3 * count + (1 + fuel) by omega,
    parent_sequence image start count (4 * groups) sequenceFetched state pointers
      constants buffers]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have invariants := parent_sequence_invariant state count (4 * groups)
    pointers constants buffers finished reachable
  rw [endPC, quad_branch image entry branchFetched finished groups bounded invariants.1]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
