import CommitGolfCandidate.UnrolledBlock
import CommitGolfCandidate.LongParentSchedule

/-! The unrolled leaf phase jumps directly to the retained parent setup, then the
unchanged long parent schedule and root serialization finish the commitment. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute commitBody

/-- The six positive parent-setup instructions, entered directly by the block exit. -/
theorem unrolled_parent_setup (state : MachineState) (messageBase : Word)
    (pc : state.pc = 4364) (nonempty : state.getReg .x19 - 1 ≠ 0) (fuel : Nat) :
    execute (submission.image .commit) (6 + fuel) (cursorNormalize state messageBase 4364) true =
      (do let result ← execute (submission.image .commit) fuel
            (cursorBaseFrame (commitParentsStartState state) messageBase) true
          return result.charge 6 0) := by
  rw [commit_parents_start (cursorNormalize state messageBase 4364) rfl nonempty,
    cursor_parent_boundary]
  rw [← pc, hoist_pc_self]

theorem unrolled_entry_frame (state : MachineState) (messageBase entry : Word) :
    ((cursorLeafFrame state messageBase).setReg .x1 4316).setPC entry =
      cursorNormalize (state.setReg .x1 4316) messageBase entry := by
  cases state
  dsimp [cursorNormalize, cursorLeafFrame, cursorBaseFrame, MachineState.setReg,
    MachineState.getReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

/-- The complete tree run after the entry jumps, with the unrolled leaf blocks. -/
theorem unrolled_schedule_linked_body (schedule : LongParentSchedule) (valid : schedule.Valid)
    (entryPC : schedule.initialPlan.entry=4388)
    (start : Word) (exitOffset loopOffset : BitVec 21)
    (leafFetched : UnrolledBlockFetched (submission.image .commit) start exitOffset loopOffset)
    (exitJump : start + 31780 + signExtend21 exitOffset = 4364)
    (loopJump : start + 31784 + signExtend21 loopOffset = start)
    (parentFetched : LongParentSchedule.Fetched (submission.image .commit) schedule)
    (state : MachineState) (count groups blocks : Nat) (messageBase : Word)
    (evenCount : count = schedule.parents groups + 1) (blockCount : count = 256 * (blocks + 1))
    (bounded : count ≤ 2 ^ 24) (positiveGroups : 0<groups)
    (leaves : CommitLeavesInvariant state count)
    (heapWindow : (state.getReg .x23).toNat + 32 * count = (state.getReg .x22).toNat)
    (total : state.getReg .x19 = BitVec.ofNat 64 count)
    (parents : ParentBuffers (state.getReg .x9) (count - 1))
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit)
      (7946 * (blocks + 1) + schedule.instructions groups + 17 + fuel)
      (((cursorLeafFrame state messageBase).setReg .x1 4316).setPC start) true =
      (do let finished ← commitBody state count
          return ⟨.success, cursorBaseFrame finished messageBase,
            22282 * (blocks + 1) + schedule.cycles groups + 17, 9 * count - 1⟩) := by
  have mainPositive : 0<schedule.width*groups := Nat.mul_pos valid.positive positiveGroups
  have residualPositive : 0<schedule.parents groups := by
    change 0<schedule.initialPlan.parents+schedule.width*groups
    omega
  have nonzero : count ≠ 0 := by omega
  have residualCount : count - 1 = schedule.parents groups := by omega
  have linkedInvariant := contiguous_link_invariant state count 4316 leaves
  have linkedWindow : ((state.setReg .x1 4316).getReg .x23).toNat + 32 * count =
      ((state.setReg .x1 4316).getReg .x22).toNat := by
    simpa [MachineState.setReg, MachineState.getReg] using heapWindow
  have progress : UnrolledProgress (state.setReg .x1 4316) (256 * (blocks + 1)) := by
    rw [← blockCount]
    exact ⟨linkedInvariant,
      by simp only [MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)], linkedWindow⟩
  have leavesRun := unrolled_loop (submission.image .commit) start exitOffset loopOffset
    leafFetched exitJump loopJump (state.setReg .x1 4316) blocks messageBase progress
    (6 + (schedule.instructions groups + (11 + fuel)))
  rw [← blockCount] at leavesRun
  have erased : commitLeaves (state.setReg .x1 4316) count = commitLeaves state count := by
    have positive := contiguous_positive_leaves state (count - 1) 4316 (state.setReg .x1 4316).pc
    rw [hoist_pc_self] at positive
    simpa only [show count - 1 + 1 = count by omega] using positive
  rw [erased] at leavesRun
  rw [show 7946 * (blocks + 1) + schedule.instructions groups + 17 + fuel =
      7946 * (blocks + 1) + (6 + (schedule.instructions groups + (11 + fuel))) by omega,
    unrolled_entry_frame, leavesRun]
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
  have parentRun := long_parent_schedule_execute_framed schedule valid parentFetched ready groups
    messageBase positiveGroups
    (by omega) (by rw [entryPC]; exact commit_parents_start_pc hashed nonempty)
    (by rw [← residualCount]; exact readyPointers)
    (commit_parents_start_constants hashed leafInvariant.oracleReady)
    (by rw [← residualCount]; exact readyBuffers) (11 + fuel)
  dsimp only [ready] at parentRun
  rw [unrolled_parent_setup hashed messageBase leafDone.1 nonempty, parentRun]
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
