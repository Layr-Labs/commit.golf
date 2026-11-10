import CommitGolfCandidate.CursorLoop
import CommitGolfCandidate.CursorRootFrame

/-! Compose the carried-input leaf loop with descending parent construction.
The exact final relation restores only the original x8/x21 registers; serialized
outputs and every memory word remain those of the retained commitment reference. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute commitBody

theorem cursor_parent_setup (state : MachineState) (messageBase : Word)
    (pc : state.pc = 4364) (nonempty : state.getReg .x19 - 1 ≠ 0) (fuel : Nat) :
    execute (submission.image .commit) (7 + fuel)
      (cursorNormalize state messageBase 4360) true =
      (do let result ← execute (submission.image .commit) fuel
            (cursorBaseFrame (commitParentsStartState state) messageBase) true
          return result.charge 7 0) := by
  have padding : execInstrBr (cursorNormalize state messageBase 4360) (.ADDI .x0 .x0 0) =
      cursorNormalize state messageBase 4364 := by
    cases state
    rfl
  rw [show 7 + fuel = 1 + (6 + fuel) by omega, heap_latch_exit _ rfl, padding,
    commit_parents_start (cursorNormalize state messageBase 4364) rfl nonempty,
    cursor_parent_boundary]
  rw [← pc, hoist_pc_self]
  simp [Execution.charge, ← Nat.add_assoc]

/-- The real parent loop has the same queries under the original-message
register frame. Its physical cost remains four instructions and eleven cycles
per node; the terminal jump is charged by the root helper separately. -/
theorem cursor_parents_execute (state : MachineState) (remaining : Nat)
    (messageBase : Word) (bounded : remaining < 2 ^ 24)
    (pc : 0 < remaining → state.pc = 4388)
    (pointers : ParentPointerInvariant state remaining)
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) remaining) (fuel : Nat) :
    execute (submission.image .commit) (4 * remaining + fuel)
      (cursorBaseFrame state messageBase) true =
      (do let finished ← commitParents state remaining
          let result ← execute (submission.image .commit) fuel
            (cursorBaseFrame finished messageBase) true
          return result.charge (11 * remaining) remaining) := by
  have framedPointers : ParentPointerInvariant (cursorBaseFrame state messageBase) remaining :=
    pointers
  have framedConstants :
      (cursorBaseFrame state messageBase).getReg .x5 = 0 ∧
      (cursorBaseFrame state messageBase).getReg .x11 = 64 ∧
      (cursorBaseFrame state messageBase).getReg .x13 = 0 := constants
  rw [commit_parents (cursorBaseFrame state messageBase) remaining bounded pc
    framedPointers framedConstants buffers]
  rw [cursor_base_parents_bind state remaining messageBase
    (fun finished => do
      let result ← execute (submission.image .commit) fuel finished true
      return result.charge (11 * remaining) remaining)]

private theorem cursor_load_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.LD destination source offset) =
      (execInstrBr state (.LD destination source offset)).setPC (pc + 4) := by
  cases destination <;> rfl

private theorem cursor_store_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.SD destination source offset) =
      (execInstrBr state (.SD destination source offset)).setPC (pc + 4) := rfl

private theorem cursor_root_pc (state : MachineState) (pc : Word) :
    commitCopyState (state.setPC pc) 79 = (commitCopyState state 79).setPC (pc + 32) := by
  rw [commit_copy_expansion, commit_copy_expansion]
  simp only [show (79 : Nat) ≠ 46 by decide, show (79 : Nat) ≠ 55 by decide,
    ite_false, ite_true, List.foldl, cursor_load_pc, cursor_store_pc]
  simp only [BitVec.add_assoc]
  rfl

/-- The retained terminal jump, root copy and halt cost twelve cycles. Their
last register frame does not affect the commitment or serialized trapdoor. -/
theorem cursor_positive_root (state : MachineState) (messageBase : Word)
    (pc : state.pc = 4404)
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (12 + fuel) (cursorBaseFrame state messageBase) true =
      pure ⟨.success, cursorBaseFrame (commitExitState (commitCopyState state 79)) messageBase, 12, 0⟩ := by
  rw [show 12 + fuel = 1 + (11 + fuel) by omega,
    pointer_parent_exit (cursorBaseFrame state messageBase) pc,
    commit_root ((cursorBaseFrame state messageBase).setPC 4412) rfl rootValid outputValid]
  simp only [pure_bind, Execution.charge]
  rw [cursor_base_pc, cursor_base_root_copy, cursor_base_exit, cursor_root_pc]
  rw [cursor_exit_pc]

/-- Full physical tree construction after salt sampling. The reference supplies
all memory refinements; the final frame changes only the original message
registers. Exact cost: 41*n+15 instructions and 104*n+8 cycles. -/
theorem cursor_body (saltFetched : CursorSaltFetched (submission.image .commit))
    (prefixFetched : CursorPrefixFetched (submission.image .commit))
    (tailFetched : CursorTailFetched (submission.image .commit))
    (state : MachineState) (count : Nat) (messageBase : Word)
    (positive : 2 ≤ count) (bounded : count ≤ 2 ^ 24)
    (leaves : CommitLeavesInvariant state count)
    (heapWindow : (state.getReg .x23).toNat + 32 * count = (state.getReg .x22).toNat)
    (total : state.getReg .x19 = BitVec.ofNat 64 count)
    (parents : ParentBuffers (state.getReg .x9) (count - 1))
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (41 * count + 15 + fuel)
      (cursorLeafFrame state messageBase) true =
      (do let finished ← commitBody state count
          return ⟨.success, cursorBaseFrame finished messageBase,
            104 * count + 8, 9 * count - 1⟩) := by
  have nonzero : count ≠ 0 := by omega
  have initialPC : state.pc = 4280 := by simpa [nonzero] using leaves.pc
  have leavesRun := cursor_leaves saltFetched prefixFetched tailFetched
    state count messageBase leaves heapWindow (7 + (4 * (count - 1) + (12 + fuel)))
  simp only [if_neg nonzero] at leavesRun
  rw [← initialPC, cursor_normalize_self_pc] at leavesRun
  rw [show 41 * count + 15 + fuel =
      37 * count + (7 + (4 * (count - 1) + (12 + fuel))) by omega, leavesRun]
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
  have readyPC : 0 < count - 1 → ready.pc = 4388 :=
    fun _ => commit_parents_start_pc hashed nonempty
  have readyHeap : ready.getReg .x9 = state.getReg .x9 :=
    (readyRegister .x9 (by simp)).trans (leafDone.2 .x9 (by simp))
  have readyOutput : ready.getReg .x26 = state.getReg .x26 :=
    (readyRegister .x26 (by simp)).trans (leafDone.2 .x26 (by simp))
  have readyBuffers : ParentBuffers (ready.getReg .x9) (count - 1) := by
    rw [readyHeap]
    exact parents
  have parentRun := cursor_parents_execute ready (count - 1) messageBase (by omega)
    readyPC readyPointers
    (commit_parents_start_constants hashed leafInvariant.oracleReady) readyBuffers (12 + fuel)
  dsimp only [ready] at parentRun
  rw [cursor_parent_setup hashed messageBase leafDone.1 nonempty, parentRun]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have parentDone := commit_parents_finished ready (count - 1) (by omega)
    readyPointers finished reachedParents
  have root : ∀ word : Fin 4,
      accessValid (finished.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true := by
    rw [parentDone.2 .x9 (by simp), readyHeap]
    exact rootValid
  have output : ∀ word : Fin 4,
      accessValid (finished.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [parentDone.2 .x26 (by simp), readyOutput]
    exact outputValid
  rw [cursor_positive_root finished messageBase (parentDone.1 (by omega)) root output]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  congr 1
  congr 1 <;> omega

end CommitGolfCandidate
