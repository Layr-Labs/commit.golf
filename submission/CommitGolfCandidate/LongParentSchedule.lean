import CommitGolfCandidate.ParentGroupComplete
import CommitGolfCandidate.CursorRootFrame
import CommitGolfCandidate.ContiguousTree
/-! Long-range jumps permit parent groups beyond conditional-branch reach. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState commitBody

/-- A short forward branch selects one of two long-range jumps. -/
theorem long_parent_branch (image : Image) (branchPC start target : Word)
    (loopOffset exitOffset : BitVec 21)
    (branchFetched : ParentGroupBranchFetched image branchPC 8)
    (loopFetched : ParentGroupExitFetched image (branchPC+8) loopOffset)
    (exitFetched : ParentGroupExitFetched image (branchPC+4) exitOffset)
    (loopJump : branchPC+8+signExtend21 loopOffset=start)
    (exitJump : branchPC+4+signExtend21 exitOffset=target)
    (state : MachineState) (remaining : Nat) (bounded : remaining<2^24)
    (pointers : ParentPointerInvariant state remaining) (fuel : Nat) :
    execute image (2+fuel) (state.setPC branchPC) true=
      (do let result ← execute image fuel
            (state.setPC (if remaining=0 then target else start)) true
          return result.charge 2 0) := by
  rw [show 2+fuel=1+(1+fuel) by omega,
    parent_group_branch image branchPC (branchPC+8) 8 branchFetched (by rfl)
      state remaining bounded pointers (1+fuel)]
  by_cases done : remaining=0
  · simp only [done,ite_true]
    rw [parent_group_exit image (branchPC+4) target exitOffset exitFetched exitJump]
    simp [Execution.charge,bind_assoc,←Nat.add_assoc]
  · simp only [done,ite_false]
    rw [parent_group_exit image (branchPC+8) start loopOffset loopFetched loopJump]
    simp [Execution.charge,bind_assoc,←Nat.add_assoc]

theorem long_parent_sequence (image : Image) (start branchPC target : Word)
    (loopOffset exitOffset : BitVec 21) (count : Nat)
    (sequenceFetched : ParentSequenceFetched image start count)
    (branchFetched : ParentGroupBranchFetched image branchPC 8)
    (loopFetched : ParentGroupExitFetched image (branchPC+8) loopOffset)
    (exitFetched : ParentGroupExitFetched image (branchPC+4) exitOffset)
    (endPC : parentSequenceEnd start count=branchPC)
    (loopJump : branchPC+8+signExtend21 loopOffset=start)
    (exitJump : branchPC+4+signExtend21 exitOffset=target)
    (state : MachineState) (remaining : Nat) (bounded : remaining<2^24)
    (pointers : ParentPointerInvariant state (remaining+count))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (remaining+count)) (fuel : Nat) :
    execute image (3*count+2+fuel) (state.setPC start) true=
      (do let finished ← commitParents state count
          let result ← execute image fuel
            (finished.setPC (if remaining=0 then target else start)) true
          return result.charge (10*count+2) count) := by
  rw [show 3*count+2+fuel=3*count+(2+fuel) by omega,
    parent_sequence image start count remaining sequenceFetched state pointers constants buffers]
  apply bind_congr_of_forall_mem_support
  intro finished reached
  have invariants := parent_sequence_invariant state count remaining pointers constants buffers finished reached
  rw [endPC,long_parent_branch image branchPC start target loopOffset exitOffset branchFetched
    loopFetched exitFetched loopJump exitJump finished remaining bounded invariants.1]
  simp [Execution.charge,← Nat.add_assoc]

theorem long_parent_loop (image : Image) (start branchPC target : Word) (loopOffset exitOffset : BitVec 21)
    (width : Nat) (positive : 0<width)
    (sequenceFetched : ParentSequenceFetched image start width)
    (branchFetched : ParentGroupBranchFetched image branchPC 8)
    (loopFetched : ParentGroupExitFetched image (branchPC+8) loopOffset)
    (exitFetched : ParentGroupExitFetched image (branchPC+4) exitOffset)
    (endPC : parentSequenceEnd start width=branchPC)
    (loopJump : branchPC+8+signExtend21 loopOffset=start)
    (exitJump : branchPC+4+signExtend21 exitOffset=target)
    (state : MachineState) (groups : Nat) (bounded : width*groups<2^24)
    (pointers : ParentPointerInvariant state (width*groups))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (width*groups)) (fuel : Nat) :
    execute image ((3*width+2)*groups+fuel)
      (state.setPC (if groups=0 then target else start)) true=
      (do let finished ← commitParents state (width*groups)
          let result ← execute image fuel (finished.setPC (target)) true
          return result.charge ((10*width+2)*groups) (width*groups)) := by
  induction groups generalizing state with
  | zero => simp [commitParents,Execution.charge]
  | succ groups ih =>
    have residual : width*(groups+1)=width*groups+width := by simp [Nat.mul_succ]
    have currentPointers : ParentPointerInvariant state (width*groups+width) := by
      rw [← residual]
      exact pointers
    have currentBuffers : ParentBuffers (state.getReg .x9) (width*groups+width) := by
      rw [← residual]
      exact buffers
    have smaller : width*groups<2^24 := by rw [residual] at bounded;omega
    simp only [Nat.succ_ne_zero,ite_false]
    rw [show (3*width+2)*(groups+1)+fuel=3*width+2+((3*width+2)*groups+fuel) by
        simp [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm],
      long_parent_sequence image start branchPC target loopOffset exitOffset width sequenceFetched branchFetched
        loopFetched exitFetched endPC loopJump exitJump
        state (width*groups) smaller currentPointers constants currentBuffers]
    rw [show width*(groups+1)=width+width*groups by simp [Nat.mul_succ,Nat.add_comm],parent_sequence_comp]
    simp only [bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    have invariants := parent_sequence_invariant state width (width*groups)
      currentPointers constants currentBuffers middle reached
    have empty : width*groups=0 ↔ groups=0 := by
      simp [Nat.mul_eq_zero,Nat.ne_of_gt positive]
    change (do let result ← execute image ((3*width+2)*groups+fuel)
                 (middle.setPC (if width*groups=0 then target else start)) true
               return result.charge (10*width+2) width)=_
    simp only [empty]
    rw [ih middle smaller invariants.1 invariants.2.1 invariants.2.2]
    simp only [bind_assoc,pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply congrArg (fun continuation => execute image fuel (finished.setPC (target)) true >>= continuation)
    funext result
    congr 1
    cases result
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem long_parent_complete (image : Image) (plan : ParentPlan)
    (planFetched : ParentPlan.Fetched image plan)
    (start branchPC : Word) (loopOffset exitOffset : BitVec 21)
    (width : Nat) (positiveWidth : 0<width)
    (sequenceFetched : ParentSequenceFetched image start width)
    (branchFetched : ParentGroupBranchFetched image branchPC 8)
    (loopFetched : ParentGroupExitFetched image (branchPC+8) loopOffset)
    (endPC : parentSequenceEnd start width=branchPC)
    (loopJump : branchPC+8+signExtend21 loopOffset=start)
    (entry : plan.finish=start)
    (exitFetched : ParentGroupExitFetched image (branchPC+4) exitOffset)
    (exitJump : branchPC+4+signExtend21 exitOffset=4412)
    (state : MachineState) (groups : Nat) (positiveGroups : 0<groups)
    (bounded : plan.parents+width*groups<2^24)
    (pointers : ParentPointerInvariant state (plan.parents+width*groups))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (plan.parents+width*groups)) (fuel : Nat) :
    execute image (plan.instructions+(3*width+2)*groups+fuel) (state.setPC plan.entry) true=
      (do let finished ← commitParents state (plan.parents+width*groups)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (plan.cycles+(10*width+2)*groups) (plan.parents+width*groups)) := by
  have remainingPositive : 0<width*groups := Nat.mul_pos positiveWidth positiveGroups
  have initialPointers : ParentPointerInvariant state (width*groups+plan.parents) := by
    rw [Nat.add_comm]
    exact pointers
  have initialBuffers : ParentBuffers (state.getReg .x9) (width*groups+plan.parents) := by
    rw [Nat.add_comm]
    exact buffers
  rw [show plan.instructions+(3*width+2)*groups+fuel=
      plan.instructions+((3*width+2)*groups+fuel) by omega,
    parent_plan_execute image plan planFetched state (width*groups) remainingPositive
      (by omega) initialPointers constants initialBuffers,parent_sequence_comp]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro middle reached
  have invariants := parent_sequence_invariant state plan.parents (width*groups)
    initialPointers constants initialBuffers middle reached
  have loop := long_parent_loop image start branchPC 4412 loopOffset exitOffset width positiveWidth
    sequenceFetched branchFetched loopFetched exitFetched endPC loopJump exitJump middle groups (by omega)
    invariants.1 invariants.2.1 invariants.2.2 fuel
  simp only [if_neg (Nat.ne_of_gt positiveGroups)] at loop
  rw [entry,loop]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished _
  simp [Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem long_parent_sequence_end (start : Word) (count : Nat) :
    parentSequenceEnd start count=start+BitVec.ofNat 64 (12*count) := by
  induction count generalizing start with
  | zero => simp [parentSequenceEnd]
  | succ count ih =>
    rw [parentSequenceEnd,ih,BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 12+BitVec.ofNat 64 (12*count)=BitVec.ofNat 64 (12*(count+1))
    rw [←BitVec.ofNat_add]
    congr 1
    omega

structure LongParentSchedule where
  initialPlan : ParentPlan
  start : Word
  branchPC : Word
  loopOffset : BitVec 21
  exitOffset : BitVec 21
  width : Nat

structure LongParentSchedule.Valid (schedule : LongParentSchedule) : Prop where
  positive : 0<schedule.width
  endPC : parentSequenceEnd schedule.start schedule.width=schedule.branchPC
  loopJump : schedule.branchPC+8+signExtend21 schedule.loopOffset=schedule.start
  entry : schedule.initialPlan.finish=schedule.start
  rootJump : schedule.branchPC+4+signExtend21 schedule.exitOffset=4412

structure LongParentSchedule.Fetched (image : Image) (schedule : LongParentSchedule) : Prop where
  plan : ParentPlan.Fetched image schedule.initialPlan
  sequence : ParentSequenceFetched image schedule.start schedule.width
  branch : ParentGroupBranchFetched image schedule.branchPC 8
  loop : ParentGroupExitFetched image (schedule.branchPC+8) schedule.loopOffset
  exit : ParentGroupExitFetched image (schedule.branchPC+4) schedule.exitOffset

def LongParentSchedule.parents (schedule : LongParentSchedule) (groups : Nat) : Nat :=
  schedule.initialPlan.parents+schedule.width*groups

def LongParentSchedule.instructions (schedule : LongParentSchedule) (groups : Nat) : Nat :=
  schedule.initialPlan.instructions+(3*schedule.width+2)*groups

def LongParentSchedule.cycles (schedule : LongParentSchedule) (groups : Nat) : Nat :=
  schedule.initialPlan.cycles+(10*schedule.width+2)*groups

/-- The schedule cost is derived from its fetched prefixes, loop and exit. -/
theorem long_parent_schedule_execute (image : Image) (schedule : LongParentSchedule)
    (valid : schedule.Valid) (fetched : schedule.Fetched image)
    (state : MachineState) (groups : Nat) (positive : 0<groups)
    (bounded : schedule.parents groups<2^24)
    (pointers : ParentPointerInvariant state (schedule.parents groups))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (schedule.parents groups)) (fuel : Nat) :
    execute image (schedule.instructions groups+fuel) (state.setPC schedule.initialPlan.entry) true=
      (do let finished ← commitParents state (schedule.parents groups)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (schedule.cycles groups) (schedule.parents groups)) :=
  long_parent_complete image schedule.initialPlan fetched.plan schedule.start schedule.branchPC
    schedule.loopOffset schedule.exitOffset schedule.width valid.positive fetched.sequence
    fetched.branch fetched.loop valid.endPC valid.loopJump valid.entry fetched.exit valid.rootJump
    state groups positive bounded pointers constants buffers fuel

/-- Carry the same inactive-register frame used by the retained leaf and root proofs. -/
theorem long_parent_schedule_execute_framed (schedule : LongParentSchedule)
    (valid : schedule.Valid) (fetched : schedule.Fetched (submission.image .commit))
    (state : MachineState) (groups : Nat) (messageBase : Word) (positive : 0<groups)
    (bounded : schedule.parents groups<2^24) (pc : state.pc=schedule.initialPlan.entry)
    (pointers : ParentPointerInvariant state (schedule.parents groups))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (schedule.parents groups)) (fuel : Nat) :
    execute (submission.image .commit) (schedule.instructions groups+fuel)
      (cursorBaseFrame state messageBase) true=
      (do let finished ← commitParents state (schedule.parents groups)
          let result ← execute (submission.image .commit) fuel
            ((cursorBaseFrame finished messageBase).setPC 4412) true
          return result.charge (schedule.cycles groups) (schedule.parents groups)) := by
  have framedPC : (cursorBaseFrame state messageBase).pc=schedule.initialPlan.entry := pc
  have run := long_parent_schedule_execute _ schedule valid fetched
    (cursorBaseFrame state messageBase) groups positive bounded pointers constants buffers fuel
  rw [← framedPC,hoist_pc_self] at run
  rw [cursor_base_parents_bind state (schedule.parents groups) messageBase
    (fun finished => do
      let result ← execute (submission.image .commit) fuel (finished.setPC 4412) true
      return result.charge (schedule.cycles groups) (schedule.parents groups))] at run
  exact run
theorem long_parent_schedule_body (schedule : LongParentSchedule) (valid : schedule.Valid)
    (entryPC : schedule.initialPlan.entry=4388) (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (latchFetched : ContiguousLatchFetched (submission.image .commit))
    (entryFetched : ContiguousEntryFetched (submission.image .commit))
    (exitFetched : ContiguousExitFetched (submission.image .commit))
    (parentFetched : LongParentSchedule.Fetched (submission.image .commit) schedule)
    (state : MachineState) (count groups : Nat) (messageBase : Word)
    (evenCount : count = schedule.parents groups + 1) (bounded : count ≤ 2 ^ 24)
    (positiveGroups : 0<groups)
    (leaves : CommitLeavesInvariant state count)
    (heapWindow : (state.getReg .x23).toNat + 32 * count = (state.getReg .x22).toNat)
    (total : state.getReg .x19 = BitVec.ofNat 64 count)
    (parents : ParentBuffers (state.getReg .x9) (count - 1))
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (35 * count + schedule.instructions groups + 20 + fuel)
      (cursorLeafFrame state messageBase) true =
      (do let finished ← commitBody state count
          return ⟨.success, cursorBaseFrame finished messageBase,
            91 * count + schedule.cycles groups + 20, 9 * count - 1⟩) := by
  have mainPositive : 0<schedule.width*groups := Nat.mul_pos valid.positive positiveGroups
  have residualPositive : 0<schedule.parents groups := by
    change 0<schedule.initialPlan.parents+schedule.width*groups
    omega
  have nonzero : count ≠ 0 := by omega
  have residualCount : count - 1 = schedule.parents groups := by omega
  have initialPC : state.pc = 4280 := by simpa [nonzero] using leaves.pc
  have linkedInvariant := contiguous_link_invariant state count 4316 leaves
  have linkedWindow : ((state.setReg .x1 4316).getReg .x23).toNat + 32 * count =
      ((state.setReg .x1 4316).getReg .x22).toNat := by
    simpa [MachineState.setReg, MachineState.getReg] using heapWindow
  have leavesRun := contiguous_leaves saltFetched prefixFetched tailFetched latchFetched
    (state.setReg .x1 4316) count messageBase linkedInvariant
    (by simp only [MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)])
    linkedWindow (7 + (schedule.instructions groups + (11 + fuel)))
  simp only [if_neg nonzero] at leavesRun
  have erased : commitLeaves (state.setReg .x1 4316) count = commitLeaves state count := by
    have positive := contiguous_positive_leaves state (count - 1) 4316 (state.setReg .x1 4316).pc
    rw [hoist_pc_self] at positive
    simpa only [show count - 1 + 1 = count by omega] using positive
  rw [erased] at leavesRun
  rw [show 35 * count + schedule.instructions groups + 20 + fuel =
      2 + (35 * count + (7 + (schedule.instructions groups + (11 + fuel)))) by omega,
    contiguous_entry _ entryFetched (cursorLeafFrame state messageBase) initialPC, contiguous_entry_frame, leavesRun]
  simp only [commitBody, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have leafDone := commit_leaves_finished state count leaves hashed reached
  have leafInvariant := commit_leaves_final_invariant state count leaves hashed reached
  let ready := commitParentsStartState hashed
  have readyRegister (reg : Reg) (member : reg ∈ [Reg.x9, .x19, .x26]) :
      ready.getReg reg = hashed.getReg reg := by
    apply commit_parents_start_register hashed reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto
  have residual : hashed.getReg .x19 - 1 = BitVec.ofNat 64 (count - 1) := by
    rw [leafDone.2 .x19 (by simp), total]
    change BitVec.ofNat 64 count - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) count 1 (by decide) (by omega)]
  have nonempty : hashed.getReg .x19 - 1 ≠ 0 := by
    rw [residual]
    intro zero
    have equal := congrArg BitVec.toNat zero
    change (count - 1) % 18446744073709551616 = 0 at equal
    omega
  have readyPointers : ParentPointerInvariant ready (count - 1) :=
    commit_parents_start_pointers hashed (count - 1) nonempty residual
  have readyHeap : ready.getReg .x9 = state.getReg .x9 :=
    (readyRegister .x9 (by simp)).trans (leafDone.2 .x9 (by simp))
  have readyOutput : ready.getReg .x26 = state.getReg .x26 :=
    (readyRegister .x26 (by simp)).trans (leafDone.2 .x26 (by simp))
  have readyBuffers : ParentBuffers (ready.getReg .x9) (count - 1) := by
    rw [readyHeap]
    exact parents
  have parentRun := long_parent_schedule_execute_framed schedule valid parentFetched ready groups messageBase positiveGroups
    (by omega) (by rw [entryPC]; exact commit_parents_start_pc hashed nonempty)
    (by rw [← residualCount]; exact readyPointers)
    (commit_parents_start_constants hashed leafInvariant.oracleReady)
    (by rw [← residualCount]; exact readyBuffers) (11 + fuel)
  dsimp only [ready] at parentRun
  rw [contiguous_parent_setup exitFetched hashed messageBase leafDone.1 nonempty, parentRun]
  rw [residualCount]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have parentDone := commit_parents_finished ready (count - 1) (by omega)
    readyPointers finished (by rw [residualCount]; exact reachedParents)
  have root : ∀ word : Fin 4,
      accessValid (finished.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true := by
    rw [parentDone.2 .x9 (by simp), readyHeap]
    exact rootValid
  have output : ∀ word : Fin 4,
      accessValid (finished.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [parentDone.2 .x26 (by simp), readyOutput]
    exact outputValid
  rw [fused_root finished messageBase root output]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  congr 1
  congr 1 <;> omega

/-- The same complete tree run, starting after the two checked entry jumps. -/
theorem long_parent_schedule_linked_body (schedule : LongParentSchedule) (valid : schedule.Valid)
    (entryPC : schedule.initialPlan.entry=4388) (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (latchFetched : ContiguousLatchFetched (submission.image .commit))
    (exitFetched : ContiguousExitFetched (submission.image .commit))
    (parentFetched : LongParentSchedule.Fetched (submission.image .commit) schedule)
    (state : MachineState) (count groups : Nat) (messageBase : Word)
    (evenCount : count = schedule.parents groups + 1) (bounded : count ≤ 2 ^ 24)
    (positiveGroups : 0<groups)
    (leaves : CommitLeavesInvariant state count)
    (heapWindow : (state.getReg .x23).toNat + 32 * count = (state.getReg .x22).toNat)
    (total : state.getReg .x19 = BitVec.ofNat 64 count)
    (parents : ParentBuffers (state.getReg .x9) (count - 1))
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (35 * count + schedule.instructions groups + 18 + fuel)
      (((cursorLeafFrame state messageBase).setReg .x1 4316).setPC 4456) true =
      (do let finished ← commitBody state count
          return ⟨.success, cursorBaseFrame finished messageBase,
            91 * count + schedule.cycles groups + 18, 9 * count - 1⟩) := by
  have mainPositive : 0<schedule.width*groups := Nat.mul_pos valid.positive positiveGroups
  have residualPositive : 0<schedule.parents groups := by
    change 0<schedule.initialPlan.parents+schedule.width*groups
    omega
  have nonzero : count ≠ 0 := by omega
  have residualCount : count - 1 = schedule.parents groups := by omega
  have initialPC : state.pc = 4280 := by simpa [nonzero] using leaves.pc
  have linkedInvariant := contiguous_link_invariant state count 4316 leaves
  have linkedWindow : ((state.setReg .x1 4316).getReg .x23).toNat + 32 * count =
      ((state.setReg .x1 4316).getReg .x22).toNat := by
    simpa [MachineState.setReg, MachineState.getReg] using heapWindow
  have leavesRun := contiguous_leaves saltFetched prefixFetched tailFetched latchFetched
    (state.setReg .x1 4316) count messageBase linkedInvariant
    (by simp only [MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)])
    linkedWindow (7 + (schedule.instructions groups + (11 + fuel)))
  simp only [if_neg nonzero] at leavesRun
  have erased : commitLeaves (state.setReg .x1 4316) count = commitLeaves state count := by
    have positive := contiguous_positive_leaves state (count - 1) 4316 (state.setReg .x1 4316).pc
    rw [hoist_pc_self] at positive
    simpa only [show count - 1 + 1 = count by omega] using positive
  rw [erased] at leavesRun
  rw [show 35 * count + schedule.instructions groups + 18 + fuel =
      35 * count + (7 + (schedule.instructions groups + (11 + fuel))) by omega,
    contiguous_entry_frame, leavesRun]
  simp only [commitBody, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have leafDone := commit_leaves_finished state count leaves hashed reached
  have leafInvariant := commit_leaves_final_invariant state count leaves hashed reached
  let ready := commitParentsStartState hashed
  have readyRegister (reg : Reg) (member : reg ∈ [Reg.x9, .x19, .x26]) :
      ready.getReg reg = hashed.getReg reg := by
    apply commit_parents_start_register hashed reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto
  have residual : hashed.getReg .x19 - 1 = BitVec.ofNat 64 (count - 1) := by
    rw [leafDone.2 .x19 (by simp), total]
    change BitVec.ofNat 64 count - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) count 1 (by decide) (by omega)]
  have nonempty : hashed.getReg .x19 - 1 ≠ 0 := by
    rw [residual]
    intro zero
    have equal := congrArg BitVec.toNat zero
    change (count - 1) % 18446744073709551616 = 0 at equal
    omega
  have readyPointers : ParentPointerInvariant ready (count - 1) :=
    commit_parents_start_pointers hashed (count - 1) nonempty residual
  have readyHeap : ready.getReg .x9 = state.getReg .x9 :=
    (readyRegister .x9 (by simp)).trans (leafDone.2 .x9 (by simp))
  have readyOutput : ready.getReg .x26 = state.getReg .x26 :=
    (readyRegister .x26 (by simp)).trans (leafDone.2 .x26 (by simp))
  have readyBuffers : ParentBuffers (ready.getReg .x9) (count - 1) := by
    rw [readyHeap]
    exact parents
  have parentRun := long_parent_schedule_execute_framed schedule valid parentFetched ready groups messageBase positiveGroups
    (by omega) (by rw [entryPC]; exact commit_parents_start_pc hashed nonempty)
    (by rw [← residualCount]; exact readyPointers)
    (commit_parents_start_constants hashed leafInvariant.oracleReady)
    (by rw [← residualCount]; exact readyBuffers) (11 + fuel)
  dsimp only [ready] at parentRun
  rw [contiguous_parent_setup exitFetched hashed messageBase leafDone.1 nonempty, parentRun]
  rw [residualCount]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have parentDone := commit_parents_finished ready (count - 1) (by omega)
    readyPointers finished (by rw [residualCount]; exact reachedParents)
  have root : ∀ word : Fin 4,
      accessValid (finished.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true := by
    rw [parentDone.2 .x9 (by simp), readyHeap]
    exact rootValid
  have output : ∀ word : Fin 4,
      accessValid (finished.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [parentDone.2 .x26 (by simp), readyOutput]
    exact outputValid
  rw [fused_root finished messageBase root output]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  congr 1
  congr 1 <;> omega


end CommitGolfCandidate
