import CommitGolfCandidate.FusedPairStep

/-! An unrolled sequence of parent queries has no intermediate branches.
Every reply is written before the next query is read. The residual natural
index supplies actual access and alignment checks separately from pointer
arithmetic; fetched instructions remain explicit premises. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

def ParentSequenceFetched (image : Image) (start : Word) : Nat → Prop
  | 0 => True
  | count + 1 =>
    ParentTripleFetched image start ∧ ParentSequenceFetched image (start + 12) count

def parentSequenceEnd (start : Word) : Nat → Word
  | 0 => start
  | count + 1 => parentSequenceEnd (start + 12) count

/-- Three instructions and ten cycles per parent, before any loop latch.
No answer consistency assumption is needed for these operational steps. -/
theorem parent_sequence (image : Image) (start : Word) (count remaining : Nat)
    (fetched : ParentSequenceFetched image start count) (state : MachineState)
    (pointers : ParentPointerInvariant state (remaining + count))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (remaining + count)) (fuel : Nat) :
    execute image (3 * count + fuel) (state.setPC start) true =
      (do let finished ← commitParents state count
          let result ← execute image fuel (finished.setPC (parentSequenceEnd start count)) true
          return result.charge (10 * count) count) := by
  induction count generalizing start state with
  | zero =>
    simp [commitParents, parentSequenceEnd, Execution.charge]
  | succ count ih =>
    have access := fused_parent_access state (remaining + (count + 1))
      (by omega) pointers buffers
    rw [show 3 * (count + 1) + fuel = 3 + (3 * count + fuel) by omega,
      fused_parent_triple image start fetched.1 state constants
        access.1 access.2.1 access.2.2.1 access.2.2.2]
    simp only [commitParents, parentSequenceEnd, bind_assoc]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (commitParentQuery state))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    let next := commitParentNextState (commitParentState state answer)
    have nextPointers : ParentPointerInvariant next (remaining + count) := by
      apply commit_parent_step_pointers state answer
      convert pointers using 1
    have nextBuffers : ParentBuffers (next.getReg .x9) (remaining + count) := by
      apply fused_parent_buffers state answer
      convert buffers using 1
    rw [ih (start + 12) fetched.2 next nextPointers
      (fused_parent_constants state answer constants) nextBuffers]
    dsimp only [next]
    simp only [bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply congrArg (fun continuation =>
      execute image fuel (finished.setPC (parentSequenceEnd (start + 12) count)) true >>=
        continuation)
    funext result
    congr 1
    cases result
    simp only [Execution.charge]
    congr 1 <;> omega

/-- Every supported result retains fixed syscall selectors and has advanced
the pointers by exactly the number of emitted parent queries. -/
theorem parent_sequence_invariant (state : MachineState) (count remaining : Nat)
    (pointers : ParentPointerInvariant state (remaining + count))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (remaining + count))
    (finished : MachineState) (reachable : finished ∈ support (commitParents state count)) :
    ParentPointerInvariant finished remaining ∧
    (finished.getReg .x5 = 0 ∧ finished.getReg .x11 = 64 ∧ finished.getReg .x13 = 0) ∧
    ParentBuffers (finished.getReg .x9) remaining := by
  induction count generalizing state with
  | zero =>
    simp only [commitParents, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨pointers, constants, buffers⟩
  | succ count ih =>
    simp only [commitParents, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    let next := commitParentNextState (commitParentState state answer)
    have nextPointers : ParentPointerInvariant next (remaining + count) := by
      apply commit_parent_step_pointers state answer
      convert pointers using 1
    have nextBuffers : ParentBuffers (next.getReg .x9) (remaining + count) := by
      apply fused_parent_buffers state answer
      convert buffers using 1
    exact ih next nextPointers (fused_parent_constants state answer constants)
      nextBuffers reached

end CommitGolfCandidate
