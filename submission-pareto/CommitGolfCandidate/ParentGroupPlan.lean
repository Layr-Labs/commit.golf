import CommitGolfCandidate.ParentGroupPrefix

/-! A finite sequence of fetched unrolled prefixes, ending at a repeated parent loop.
A positive residual proves each actual forward branch is taken. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

inductive ParentPlan where
  | done (target : Word)
  | stage (start : Word) (count : Nat) (branchPC : Word) (offset : BitVec 13) (tail : ParentPlan)

def ParentPlan.entry : ParentPlan → Word
  | .done target => target
  | .stage start _ _ _ _ => start

def ParentPlan.finish : ParentPlan → Word
  | .done target => target
  | .stage _ _ _ _ tail => tail.finish

def ParentPlan.parents : ParentPlan → Nat
  | .done _ => 0
  | .stage _ count _ _ tail => count+tail.parents

def ParentPlan.instructions : ParentPlan → Nat
  | .done _ => 0
  | .stage _ count _ _ tail => 3*count+1+tail.instructions

def ParentPlan.cycles : ParentPlan → Nat
  | .done _ => 0
  | .stage _ count _ _ tail => 10*count+1+tail.cycles

def ParentPlan.Fetched (image : Image) : ParentPlan → Prop
  | .done _ => True
  | .stage start count branchPC offset tail =>
      ParentSequenceFetched image start count ∧ ParentGroupBranchFetched image branchPC offset ∧
      parentSequenceEnd start count=branchPC ∧ branchPC+signExtend13 offset=tail.entry ∧
      ParentPlan.Fetched image tail

/-- Every prefix executes its delivered triples and actual branch before the next stage. -/
theorem parent_plan_execute (image : Image) (plan : ParentPlan)
    (fetched : ParentPlan.Fetched image plan)
    (state : MachineState) (remaining : Nat) (positive : 0<remaining)
    (bounded : remaining+plan.parents<2^24)
    (pointers : ParentPointerInvariant state (remaining+plan.parents))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (remaining+plan.parents)) (fuel : Nat) :
    execute image (plan.instructions+fuel) (state.setPC plan.entry) true=
      (do let finished ← commitParents state plan.parents
          let result ← execute image fuel (finished.setPC plan.finish) true
          return result.charge plan.cycles plan.parents) := by
  induction plan generalizing state remaining with
  | done target => simp [ParentPlan.instructions,ParentPlan.entry,ParentPlan.finish,ParentPlan.parents,
      ParentPlan.cycles,commitParents,Execution.charge]
  | stage start count branchPC offset tail ih =>
    change remaining+(count+tail.parents)<2^24 at bounded
    change ParentPointerInvariant state (remaining+(count+tail.parents)) at pointers
    change ParentBuffers (state.getReg .x9) (remaining+(count+tail.parents)) at buffers
    have reorder : remaining+(count+tail.parents)=(remaining+tail.parents)+count := by omega
    have currentPointers : ParentPointerInvariant state ((remaining+tail.parents)+count) := by
      rw [← reorder]
      exact pointers
    have currentBuffers : ParentBuffers (state.getReg .x9) ((remaining+tail.parents)+count) := by
      rw [← reorder]
      exact buffers
    change execute image (3*count+1+tail.instructions+fuel) (state.setPC start) true=
      (do let finished ← commitParents state (count+tail.parents)
          let result ← execute image fuel (finished.setPC tail.finish) true
          return result.charge (10*count+1+tail.cycles) (count+tail.parents))
    rw [show 3*count+1+tail.instructions+fuel=3*count+1+(tail.instructions+fuel) by omega,
      parent_group_prefix image start branchPC tail.entry offset count fetched.1 fetched.2.1
        fetched.2.2.1 fetched.2.2.2.1 state (remaining+tail.parents) (by omega) (by omega)
        currentPointers constants currentBuffers,parent_sequence_comp]
    simp only [bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    have invariants := parent_sequence_invariant state count (remaining+tail.parents)
      currentPointers constants currentBuffers middle reached
    rw [ih fetched.2.2.2.2 middle remaining positive (by omega) invariants.1 invariants.2.1 invariants.2.2]
    simp only [bind_assoc,pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply congrArg (fun continuation => execute image fuel (finished.setPC tail.finish) true >>= continuation)
    funext result
    cases result
    simp [Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end CommitGolfCandidate
