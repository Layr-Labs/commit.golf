import CommitGolfCandidate.FusedPairStep

/-! Induction on pairs composes the two-parent body. The reference residual
index remains ghost state, while execution terminates at the pair exit jump. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

/-- Each pair costs seven instructions, twenty-one cycles and two queries.
Completion stops before the once-only jump at PC4344. -/
theorem fused_pairs (image : Image)
    (firstFetched : ParentTripleFetched image 4316)
    (secondFetched : ParentTripleFetched image 4328)
    (branchFetched : PairedBranchFetched image)
    (state : MachineState) (pairs : Nat) (bounded : 2 * pairs < 2 ^ 24)
    (pointers : ParentPointerInvariant state (2 * pairs))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (2 * pairs)) (fuel : Nat) :
    execute image (7 * pairs + fuel)
      (state.setPC (if pairs = 0 then 4344 else 4316)) true =
      (do let finished ← commitParents state (2 * pairs)
          let result ← execute image fuel (finished.setPC 4344) true
          return result.charge (21 * pairs) (2 * pairs)) := by
  induction pairs generalizing state with
  | zero => simp [commitParents, Execution.charge]
  | succ pairs ih =>
    simp only [show pairs + 1 ≠ 0 by omega, ite_false]
    rw [show 7 * (pairs + 1) + fuel = 7 + (7 * pairs + fuel) by omega,
      fused_pair_step image firstFetched secondFetched branchFetched state pairs
        bounded pointers constants buffers]
    rw [show 2 * (pairs + 1) = (2 * pairs + 1) + 1 by omega]
    simp only [commitParents, bind_assoc]
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
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (commitParentQuery first))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer₂
    change BitVec 256 at answer₂
    let second := commitParentNextState (commitParentState first answer₂)
    have secondPointers : ParentPointerInvariant second (2 * pairs) :=
      commit_parent_step_pointers first answer₂ (2 * pairs) firstPointers
    have secondConstants := fused_parent_constants first answer₂
      (fused_parent_constants state answer₁ constants)
    have secondBuffers := fused_parent_buffers first answer₂ (2 * pairs) firstBuffers
    rw [ih second (by omega) secondPointers secondConstants secondBuffers]
    dsimp only [first, second]
    simp only [bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply congrArg (fun continuation =>
      execute image fuel (finished.setPC 4344) true >>= continuation)
    funext result
    congr 1
    cases result
    simp only [Execution.charge]
    congr 1 <;> omega

end CommitGolfCandidate
