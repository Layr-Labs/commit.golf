import CommitGolfCandidate.ParentSequence

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

def octBranchPC (entry : Bool) : Word := if entry then 4648 else 4752

def OctBranchFetched (image : Image) (entry : Bool) : Prop :=
  ∀ state : MachineState,
    state.pc = octBranchPC entry →
      fetch image state = some (.base (.BNE .x12 .x9 (if entry then 8 else 8096)))

theorem oct_branch (image : Image) (entry : Bool)
    (fetched : OctBranchFetched image entry) (state : MachineState) (groups : Nat)
    (bounded : 8 * groups < 2 ^ 24)
    (pointers : ParentPointerInvariant state (8 * groups)) (fuel : Nat) :
    execute image (1 + fuel) (state.setPC (octBranchPC entry)) true =
      (do let result ← execute image fuel
            (state.setPC (if groups = 0 then octBranchPC entry + 4 else 4656)) true
          return result.charge 1 0) := by
  have done : state.getReg .x12 = state.getReg .x9 ↔ groups = 0 := by
    rw [pointers.2, parent_pointer_done_iff _ (8 * groups) bounded]
    omega
  change state.regs .x12 = state.regs .x9 ↔ groups = 0 at done
  have stepped : ordinaryStep (state.setPC (octBranchPC entry))
      (.base (.BNE .x12 .x9 (if entry then 8 else 8096))) =
      some (state.setPC (if groups = 0 then octBranchPC entry + 4 else 4656)) := by
    cases entry <;>
      simp [octBranchPC, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
        signExtend13, MachineState.getReg, MachineState.getReg_setPC,
        MachineState.setPC, done] <;>
      split <;> simp_all
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
    (fetched (state.setPC (octBranchPC entry)) rfl) stepped]
  rfl

theorem oct_sequence_branch (image : Image) (start : Word) (count : Nat)
    (entry : Bool) (sequenceFetched : ParentSequenceFetched image start count)
    (branchFetched : OctBranchFetched image entry)
    (endPC : parentSequenceEnd start count = octBranchPC entry)
    (state : MachineState) (groups : Nat) (bounded : 8 * groups < 2 ^ 24)
    (pointers : ParentPointerInvariant state (8 * groups + count))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (8 * groups + count)) (fuel : Nat) :
    execute image (3 * count + 1 + fuel) (state.setPC start) true =
      (do let finished ← commitParents state count
          let result ← execute image fuel
            (finished.setPC (if groups = 0 then octBranchPC entry + 4 else 4656)) true
          return result.charge (10 * count + 1) count) := by
  rw [show 3 * count + 1 + fuel = 3 * count + (1 + fuel) by omega,
    parent_sequence image start count (8 * groups) sequenceFetched state pointers
      constants buffers]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have invariants := parent_sequence_invariant state count (8 * groups)
    pointers constants buffers finished reachable
  rw [endPC, oct_branch image entry branchFetched finished groups bounded invariants.1]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
