import CommitGolfCandidate.OuterFrame
/-! The real heap-end branch controls leaf execution. Virtual x20 is used only
by the reference refinement, then erased before the parent setup overwrites it. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Three fetched ordinary instructions advance both pointers and branch on heap end. -/
theorem heap_latch_execute (state : MachineState) (pc : state.pc=4348) (fuel : Nat) :
    execute (submission.image .commit) (3+fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (outerPhysicalNextState state) true
          return result.charge 3 0) := by
  apply outer_latch_execute _ state fuel pc
  intro i hi
  apply commit_fetch _ (63+i) _ (by omega)
  · interval_cases i <;> simp [outerLatchPrefix,outerLatchInstructions,execInstrBr,pc,MachineState.setPC]
  · interval_cases i <;> rfl

/-- No physical counter is incremented. The old reference increment is normalized away. -/
theorem heap_latch_normalized (state : MachineState) (counter : state.getReg .x20=0) :
    outerPhysicalNextState state =
      outerNormalize (commitPositionNextState state)
        (if BitVec.ult (state.getReg .x23+32) (state.getReg .x22) then 4280 else 4360) := by
  cases state
  dsimp [outerPhysicalNextState,outerNormalize,commitPositionNextState,MachineState.getReg,
    MachineState.setReg,MachineState.setPC] at counter ⊢
  congr 1
  funext reg
  cases reg <;> simp_all

set_option maxHeartbeats 1000000 in
/-- Load the salt into the consumed prefix, stream eight compression queries,
store the digest, and advance. The exact cost is 39 instructions and 95 cycles. -/
theorem heap_latch_position (state : MachineState) (pc : state.pc = 4280)
    (scratch : state.getReg .x21 = state.getReg .x8 - 32)
    (above : 32 ≤ (state.getReg .x8).toNat)
    (oracleReady : CommitLeafOracleReady state) (blockCounter : state.getReg .x28=0)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heapValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (messageValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (remaining : Nat) (zeroCounter : state.getReg .x20=0)
    (window : (state.getReg .x23).toNat+32*(remaining+1)=(state.getReg .x22).toNat)
    (fuel : Nat) :
    execute (submission.image .commit) (39 + fuel) state true =
      (do let finished ← commitPositionRun state
          let result ← execute (submission.image .commit) fuel (outerNormalize finished (if remaining=0 then 4360 else 4280)) true
          return result.charge 95 8) := by
  let ready := commitPositionState state
  let initialized := commitLeafReadyState ready
  obtain ⟨aligned, bounded⟩ := commit_leaf_source_range state messageValid
  have source : state.getReg .x8 = BitVec.ofNat 64 (state.getReg .x8).toNat := by
    simp
  have chainPrefix : state.getReg .x21 = BitVec.ofNat 64 ((state.getReg .x8).toNat - 32) := by
    rw [scratch]
    calc
      state.getReg .x8 - 32 = BitVec.ofNat 64 (state.getReg .x8).toNat - BitVec.ofNat 64 32 :=
        congrArg (fun value : Word => value - 32) source
      _ = _ := BitVec.ofNat_sub_ofNat_of_le (w := 64) _ 32 (by decide) above
  have scratchValid : ∀ word : Fin 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [chainPrefix, ← BitVec.ofNat_add]
    have small : (state.getReg .x8).toNat - 32 + 8 * word.val < 2^64 := by
      have hw := word.isLt; unfold MEMORY_BYTES at bounded; omega
    simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · have hw := word.isLt; omega
    · omega
  have copyPC : (commitCopyState state 46).pc = 4312 := by rw [commit_copy_pc, pc]; rfl
  have readyPC : ready.pc = 4456 := rfl
  have readyLink : ready.getReg .x1 = 4316 := by
    simp only [ready, commitPositionState, commitLeafCallState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)]
  have readySource : ready.getReg .x8 = state.getReg .x8 :=
    commit_position_register state .x8 (by decide) (by decide)
  have readyOracle : CommitLeafOracleReady ready := by
    rcases oracleReady with ⟨r5,r11,r13⟩
    exact ⟨(commit_position_register state .x5 (by decide) (by decide)).trans r5,
      (commit_position_register state .x11 (by decide) (by decide)).trans r11,
      (commit_position_register state .x13 (by decide) (by decide)).trans r13⟩
  have readyHeap : rangeValid (ready.getReg .x23) 32 = true ∧
      (ready.getReg .x23).toNat % 8 = 0 := by
    rw [commit_position_register state .x23 (by decide) (by decide)]
    exact commit_leaf_heap_range state heapValid
  have leafRun := commit_leaf_subroutine ready readyPC readyLink readyOracle
    (by simpa [readySource] using aligned) (by simpa [readySource] using above)
    (by simpa [readySource] using bounded) readyHeap (3 + fuel) true
  dsimp only [ready, commitPositionState] at leafRun
  rw [show 39 + fuel = 8 + (1 + (27 + (3 + fuel))) by omega,
    commit_copy state 46 (Or.inl rfl) pc (by
      change ∀ word : Fin 4, accessValid (state.getReg .x18+BitVec.ofNat 64 (0+8*word.val)) 8=true
      simpa only [Nat.zero_add] using saltValid) scratchValid,
    commit_leaf_call _ copyPC, leafRun]
  simp only [commitPositionRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf reached
  have leafHeap : leaf.getReg .x23 = state.getReg .x23 := by
    exact ((commit_leaf_loop_registers initialized 8 leaf reached).2 .x23 (by decide)).trans
      (commit_position_register state .x23 (by decide) (by decide))
  have leafEnd : leaf.getReg .x22 = state.getReg .x22 := by
    exact (outer_leaf_end_preserved initialized leaf 8 reached).trans
      (commit_position_register state .x22 (by decide) (by decide))
  have leafCounter : leaf.getReg .x20=0 := by
    exact ((commit_leaf_loop_registers initialized 8 leaf reached).2 .x20 (by decide)).trans
      ((commit_position_register state .x20 (by decide) (by decide)).trans zeroCounter)
  have branch : BitVec.ult (leaf.getReg .x23+32) (leaf.getReg .x22)=decide (0<remaining) := by
    rw [leafHeap,leafEnd]
    exact outer_heap_latch _ _ remaining window
  rw [heap_latch_execute (leaf.setPC 4348) rfl]
  rw [heap_latch_normalized (leaf.setPC 4348) leafCounter]
  simp only [MachineState.getReg_setPC]
  rw [branch]
  by_cases empty : remaining=0 <;> simp [empty,Nat.pos_of_ne_zero,Execution.charge,← Nat.add_assoc]


/-- Normalization changes only the reference counter and program counter. -/
theorem heap_normalize_register (state : MachineState) (pc : Word) (reg : Reg)
    (notCounter : reg ≠ .x20) :
    (outerNormalize state pc).getReg reg=state.getReg reg := by
  simp only [outerNormalize,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCounter)]

/-- At the ABI entry the physical counter is already zero. -/
theorem heap_normalize_state (state : MachineState) (pc : Word)
    (counter : state.getReg .x20=0) :
    outerNormalize state pc=state.setPC pc := by
  cases state
  dsimp [outerNormalize,MachineState.getReg,MachineState.setReg,MachineState.setPC] at counter ⊢
  congr 1
  funext reg
  cases reg <;> simp_all

attribute [local irreducible] execute commitPositionRun

/-- The saved end pointer justifies every actual branch. The reference loop's
virtual counter is retained only to reuse memory refinement and erased from
physical states. Exact cost: 39 instructions, 95 cycles and eight queries per leaf. -/
theorem heap_latch_leaves (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining)
    (window : (state.getReg .x23).toNat+32*remaining=(state.getReg .x22).toNat)
    (fuel : Nat) :
    execute (submission.image .commit) (39*remaining+fuel)
      (outerNormalize state (if remaining=0 then 4360 else 4280)) true =
      (do let finished ← commitLeaves state remaining
          let result ← execute (submission.image .commit) fuel (outerNormalize finished 4360) true
          return result.charge (95*remaining) (8*remaining)) := by
  induction remaining generalizing state with
  | zero => simp [commitLeaves,Execution.charge]
  | succ remaining ih =>
    let physical := outerNormalize state 4280
    have reg (r : Reg) (h : r ≠ .x20) : physical.getReg r=state.getReg r :=
      heap_normalize_register state 4280 r h
    have scratch : physical.getReg .x21=physical.getReg .x8-32 := by
      rw [reg .x21 (by decide),reg .x8 (by decide)]; exact invariant.scratch
    have ready : CommitLeafOracleReady physical := by
      exact ⟨(reg .x5 (by decide)).trans invariant.oracleReady.1,
        (reg .x11 (by decide)).trans invariant.oracleReady.2.1,
        (reg .x13 (by decide)).trans invariant.oracleReady.2.2⟩
    have physicalWindow : (physical.getReg .x23).toNat+32*(remaining+1)=
        (physical.getReg .x22).toNat := by
      rw [reg .x23 (by decide),reg .x22 (by decide)]; exact window
    simp only [show remaining+1 ≠ 0 by omega,ite_false]
    rw [show 39*(remaining+1)+fuel=39+(39*remaining+fuel) by omega,
      heap_latch_position physical rfl scratch
        (by rw [reg .x8 (by decide)]; exact invariant.sourceAbove) ready
        ((reg .x28 (by decide)).trans invariant.blockCounter)
        (fun word => by rw [reg .x18 (by decide)]; exact invariant.salts word.val (by omega))
        (fun word => by rw [reg .x23 (by decide)]; exact invariant.heap word.val (by omega))
        (fun word bound => by rw [reg .x8 (by decide)]; exact invariant.message word (by omega))
        remaining (by rfl) physicalWindow]
    simp only [commitLeaves,bind_assoc]
    change (do let next ← commitPositionRun ((state.setReg .x20 0).setPC 4280)
               let result ← execute (submission.image .commit) (39*remaining+fuel)
                 (outerNormalize next (if remaining=0 then 4360 else 4280)) true
               return result.charge 95 8) = _
    rw [outer_position_run_pc]
    rw [outer_position_bind state 0 (if remaining=0 then 4360 else 4280)
      (fun next => do
        let result ← execute (submission.image .commit) (39*remaining+fuel) next true
        return result.charge 95 8)]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (commit_leaves_next_invariant state next remaining invariant reached)
      (outer_heap_progress_next state next remaining window reached)]
    simp [Execution.charge,Nat.mul_add,Nat.add_comm,Nat.add_left_comm]

/-- The exit-only NOP is paid once and restores the retained parent entry PC. -/
theorem heap_latch_exit (state : MachineState) (pc : state.pc=4360) (fuel : Nat) :
    execute (submission.image .commit) (1+fuel) state true =
      (do let result ← execute (submission.image .commit) fuel
            (execInstrBr state (.ADDI .x0 .x0 0)) true
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state=some (.base (.ADDI .x0 .x0 0)) := by
    apply commit_fetch _ 66 _ (by decide) pc; rfl
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched (by rfl)]
  rfl

/-- Exit padding and parent initialization erase the physical counter frame.
The NOP costs one and the positive parent setup costs six, exactly once. -/
theorem heap_latch_parent_setup (state : MachineState) (pc : state.pc=4364)
    (nonempty : state.getReg .x19-1 ≠ 0) (fuel : Nat) :
    execute (submission.image .commit) (7+fuel) (outerNormalize state 4360) true =
      (do let result ← execute (submission.image .commit) fuel (commitParentsStartState state) true
          return result.charge 7 0) := by
  let afterNop := execInstrBr (outerNormalize state 4360) (.ADDI .x0 .x0 0)
  have nextPC : afterNop.pc=4364 := rfl
  have nextCount : afterNop.getReg .x19=state.getReg .x19 := rfl
  rw [show 7+fuel=1+(6+fuel) by omega,heap_latch_exit _ rfl,
    commit_parents_start afterNop nextPC (by rw [nextCount]; exact nonempty)]
  rw [outer_exit_parent_frame]
  rw [← pc,hoist_pc_self]
  simp [Execution.charge,← Nat.add_assoc]

end CommitGolfCandidate
