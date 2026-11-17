import CommitGolfCandidate.ParentGroupPlan

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

def ParentGroupExitFetched (image : Image) (pc : Word) (offset : BitVec 21) : Prop :=
  ∀ state : MachineState, state.pc=pc → fetch image state=some (.base (.JAL .x0 offset))

theorem parent_group_exit (image : Image) (pc target : Word) (offset : BitVec 21)
    (fetched : ParentGroupExitFetched image pc offset) (jump : pc+signExtend21 offset=target)
    (state : MachineState) (fuel : Nat) :
    execute image (1+fuel) (state.setPC pc) true=
      (do let result ← execute image fuel (state.setPC target) true
          return result.charge 1 0) := by
  have stepped : ordinaryStep (state.setPC pc) (.base (.JAL .x0 offset))=
      some (state.setPC target) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,MachineState.setPC,jump]
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ (fetched (state.setPC pc) rfl) stepped]
  rfl

theorem parent_group_complete (image : Image) (plan : ParentPlan)
    (planFetched : ParentPlan.Fetched image plan)
    (start branchPC : Word) (branchOffset : BitVec 13) (exitOffset : BitVec 21)
    (width : Nat) (positiveWidth : 0<width)
    (sequenceFetched : ParentSequenceFetched image start width)
    (branchFetched : ParentGroupBranchFetched image branchPC branchOffset)
    (endPC : parentSequenceEnd start width=branchPC)
    (loopJump : branchPC+signExtend13 branchOffset=start)
    (entry : plan.finish=start)
    (exitFetched : ParentGroupExitFetched image (branchPC+4) exitOffset)
    (exitJump : branchPC+4+signExtend21 exitOffset=4412)
    (state : MachineState) (groups : Nat) (positiveGroups : 0<groups)
    (bounded : plan.parents+width*groups<2^24)
    (pointers : ParentPointerInvariant state (plan.parents+width*groups))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (plan.parents+width*groups)) (fuel : Nat) :
    execute image (plan.instructions+(3*width+1)*groups+1+fuel) (state.setPC plan.entry) true=
      (do let finished ← commitParents state (plan.parents+width*groups)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (plan.cycles+(10*width+1)*groups+1) (plan.parents+width*groups)) := by
  have remainingPositive : 0<width*groups := Nat.mul_pos positiveWidth positiveGroups
  have initialPointers : ParentPointerInvariant state (width*groups+plan.parents) := by
    rw [Nat.add_comm]
    exact pointers
  have initialBuffers : ParentBuffers (state.getReg .x9) (width*groups+plan.parents) := by
    rw [Nat.add_comm]
    exact buffers
  rw [show plan.instructions+(3*width+1)*groups+1+fuel=
      plan.instructions+((3*width+1)*groups+(1+fuel)) by omega,
    parent_plan_execute image plan planFetched state (width*groups) remainingPositive
      (by omega) initialPointers constants initialBuffers,parent_sequence_comp]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro middle reached
  have invariants := parent_sequence_invariant state plan.parents (width*groups)
    initialPointers constants initialBuffers middle reached
  have loop := parent_group_loop image start branchPC branchOffset width positiveWidth
    sequenceFetched branchFetched endPC loopJump middle groups (by omega)
    invariants.1 invariants.2.1 invariants.2.2 (1+fuel)
  simp only [if_neg (Nat.ne_of_gt positiveGroups)] at loop
  rw [entry,loop]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished _
  rw [parent_group_exit image (branchPC+4) 4412 exitOffset exitFetched exitJump finished fuel]
  simp [Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end CommitGolfCandidate
