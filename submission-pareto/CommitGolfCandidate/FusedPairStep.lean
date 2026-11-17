import CommitGolfCandidate.FusedParentTriple

/-! Two parents share one loop branch. A natural even residual count proves
both real memory accesses and the end-pointer test; no machine counter is used. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def PairedBranchFetched (image : Image) : Prop :=
  ∀ state : MachineState,
    state.pc = 4340 → fetch image state = some (.base (.BNE .x12 .x9 8168))

theorem fused_parent_access (state : MachineState) (remaining : Nat)
    (positive : 0 < remaining) (pointers : ParentPointerInvariant state remaining)
    (buffers : ParentBuffers (state.getReg .x9) remaining) :
    rangeValid (state.getReg .x10) 64 = true ∧
    rangeValid (state.getReg .x12) 32 = true ∧
    (state.getReg .x10).toNat % 8 = 0 ∧
    (state.getReg .x12).toNat % 8 = 0 := by
  have current := buffers remaining positive (by omega)
  simp only [parent_pointer_shift] at current
  rw [pointers.1, pointers.2]
  exact current

theorem fused_parent_constants (state : MachineState) (answer : BitVec 256)
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0) :
    (commitParentNextState (commitParentState state answer)).getReg .x5 = 0 ∧
    (commitParentNextState (commitParentState state answer)).getReg .x11 = 64 ∧
    (commitParentNextState (commitParentState state answer)).getReg .x13 = 0 := by
  rw [commit_parent_step_register state answer .x5 (by simp),
    commit_parent_step_register state answer .x11 (by simp),
    commit_parent_step_register state answer .x13 (by simp)]
  exact constants

theorem fused_parent_buffers (state : MachineState) (answer : BitVec 256)
    (remaining : Nat) (buffers : ParentBuffers (state.getReg .x9) (remaining + 1)) :
    ParentBuffers ((commitParentNextState (commitParentState state answer)).getReg .x9)
      remaining := by
  rw [commit_parent_step_register state answer .x9 (by simp)]
  exact fun node positive bound => buffers node positive (by omega)

/-- The pair latch costs one real branch and tests the twice-decremented pointer. -/
theorem fused_pair_branch (image : Image) (fetched : PairedBranchFetched image)
    (state : MachineState) (pairs : Nat) (bounded : 2 * pairs < 2 ^ 24)
    (pointers : ParentPointerInvariant state (2 * pairs)) (fuel : Nat) :
    execute image (1 + fuel) (state.setPC 4340) true =
      (do let result ← execute image fuel
            (state.setPC (if pairs = 0 then 4344 else 4316)) true
          return result.charge 1 0) := by
  have done : state.getReg .x12 = state.getReg .x9 ↔ pairs = 0 := by
    rw [pointers.2, parent_pointer_done_iff _ (2 * pairs) bounded]
    omega
  change state.regs .x12 = state.regs .x9 ↔ pairs = 0 at done
  have stepped : ordinaryStep (state.setPC 4340) (.base (.BNE .x12 .x9 8168)) =
      some (state.setPC (if pairs = 0 then 4344 else 4316)) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      MachineState.getReg, MachineState.getReg_setPC, MachineState.setPC, done]
    split <;> simp_all
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
    (fetched (state.setPC 4340) rfl) stepped]
  rfl

/-- Seven instructions and twenty-one cycles emit exactly two reference queries. -/
theorem fused_pair_step (image : Image)
    (firstFetched : ParentTripleFetched image 4316)
    (secondFetched : ParentTripleFetched image 4328)
    (branchFetched : PairedBranchFetched image)
    (state : MachineState) (pairs : Nat) (bounded : 2 * (pairs + 1) < 2 ^ 24)
    (pointers : ParentPointerInvariant state (2 * (pairs + 1)))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (2 * (pairs + 1))) (fuel : Nat) :
    execute image (7 + fuel) (state.setPC 4316) true =
      (do let answer₁ ← World.query (.inr (commitParentQuery state))
          let first := commitParentNextState (commitParentState state answer₁)
          let answer₂ ← World.query (.inr (commitParentQuery first))
          let second := commitParentNextState (commitParentState first answer₂)
          let result ← execute image fuel
            (second.setPC (if pairs = 0 then 4344 else 4316)) true
          return result.charge 21 2) := by
  have firstAccess := fused_parent_access state (2 * (pairs + 1)) (by omega) pointers buffers
  rw [show 7 + fuel = 3 + (3 + (1 + fuel)) by omega,
    fused_parent_triple image 4316 firstFetched state constants
      firstAccess.1 firstAccess.2.1 firstAccess.2.2.1 firstAccess.2.2.2]
  simp only [bind_assoc]
  apply congrArg (fun tail =>
    (liftM (World.query (.inr (commitParentQuery state))) :
      OracleComp World (BitVec 256)) >>= tail)
  funext answer₁
  change BitVec 256 at answer₁
  let first := commitParentNextState (commitParentState state answer₁)
  have firstPointers : ParentPointerInvariant first (2 * pairs + 1) := by
    apply commit_parent_step_pointers state answer₁
    convert pointers using 1 <;> congr 1 <;> omega
  have firstBuffers : ParentBuffers (first.getReg .x9) (2 * pairs + 1) := by
    apply fused_parent_buffers state answer₁
    convert buffers using 1 <;> congr 1 <;> omega
  have secondAccess := fused_parent_access first (2 * pairs + 1) (by omega)
    firstPointers firstBuffers
  change (do let result ← execute image (3 + (1 + fuel)) (first.setPC 4328) true
             return result.charge 10 1) = _
  rw [fused_parent_triple image 4328 secondFetched first
    (fused_parent_constants state answer₁ constants)
    secondAccess.1 secondAccess.2.1 secondAccess.2.2.1 secondAccess.2.2.2]
  simp only [bind_assoc]
  apply congrArg (fun tail =>
    (liftM (World.query (.inr (commitParentQuery first))) :
      OracleComp World (BitVec 256)) >>= tail)
  funext answer₂
  change BitVec 256 at answer₂
  let second := commitParentNextState (commitParentState first answer₂)
  have secondPointers : ParentPointerInvariant second (2 * pairs) :=
    commit_parent_step_pointers first answer₂ (2 * pairs) firstPointers
  change (do let result ← execute image (1 + fuel) (second.setPC 4340) true
             return (result.charge 10 1).charge 10 1) = _
  rw [fused_pair_branch image branchFetched second pairs (by omega) secondPointers]
  simp [Execution.charge, ← Nat.add_assoc, first, second]

end CommitGolfCandidate
