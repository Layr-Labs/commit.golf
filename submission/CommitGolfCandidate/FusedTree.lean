import CommitGolfCandidate.FusedLoop
import CommitGolfCandidate.FusedParents
import CommitGolfCandidate.CursorRootFrame

/-! Fused leaves and peeled paired parents refine the retained salted tree.
Only x8/x21 are framed at the final machine state; all memory and serialized
outputs remain those of the reference. Every new fetch premise is explicit. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute commitBody

structure FusedParentFetched (image : Image) : Prop where
  peeled : ParentTripleFetched image 4388
  first : ParentTripleFetched image 4316
  second : ParentTripleFetched image 4328
  peeledBranch : PeeledBranchFetched image
  pairBranch : PairedBranchFetched image
  exit : ParentExitFetched image

def FusedExitFetched (image : Image) : Prop :=
  ∀ state : MachineState,
    state.pc = 4564 → fetch image state = some (.base (.JAL .x0 2096952))

theorem fused_leaf_exit (image : Image) (fetched : FusedExitFetched image)
    (state : MachineState) (pc : state.pc = 4564) (fuel : Nat) :
    execute image (1 + fuel) state true =
      (do let result ← execute image fuel (state.setPC 4364) true
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.JAL .x0 2096952)) =
      some (state.setPC 4364) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      pc, MachineState.setReg]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetched state pc) stepped]
  rfl

/-- The final leaf pays one exit jump and six positive parent-setup instructions. -/
theorem fused_parent_setup (fetched : FusedExitFetched (submission.image .commit))
    (state : MachineState) (messageBase : Word)
    (pc : state.pc = 4364) (nonempty : state.getReg .x19 - 1 ≠ 0) (fuel : Nat) :
    execute (submission.image .commit) (7 + fuel)
      (cursorNormalize state messageBase 4564) true =
      (do let result ← execute (submission.image .commit) fuel
            (cursorBaseFrame (commitParentsStartState state) messageBase) true
          return result.charge 7 0) := by
  rw [show 7 + fuel = 1 + (6 + fuel) by omega,
    fused_leaf_exit _ fetched _ rfl]
  have padding : (cursorNormalize state messageBase 4564).setPC 4364 =
      cursorNormalize state messageBase 4364 := rfl
  rw [padding, commit_parents_start (cursorNormalize state messageBase 4364) rfl nonempty,
    cursor_parent_boundary]
  rw [← pc, hoist_pc_self]
  simp [Execution.charge, ← Nat.add_assoc]

theorem fused_parents_execute (fetched : FusedParentFetched (submission.image .commit))
    (state : MachineState) (pairs : Nat) (messageBase : Word)
    (bounded : 2 * pairs + 1 < 2 ^ 24) (pc : state.pc = 4388)
    (pointers : ParentPointerInvariant state (2 * pairs + 1))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (2 * pairs + 1)) (fuel : Nat) :
    execute (submission.image .commit) (7 * pairs + 5 + fuel)
      (cursorBaseFrame state messageBase) true =
      (do let finished ← commitParents state (2 * pairs + 1)
          let result ← execute (submission.image .commit) fuel
            ((cursorBaseFrame finished messageBase).setPC 4412) true
          return result.charge (21 * pairs + 12) (2 * pairs + 1)) := by
  have framedPC : (cursorBaseFrame state messageBase).pc = 4388 := pc
  have run := fused_parents _ fetched.peeled fetched.first fetched.second
    fetched.peeledBranch fetched.pairBranch fetched.exit
    (cursorBaseFrame state messageBase) pairs bounded pointers constants buffers fuel
  rw [← framedPC, hoist_pc_self] at run
  rw [cursor_base_parents_bind state (2 * pairs + 1) messageBase
    (fun finished => do
      let result ← execute (submission.image .commit) fuel (finished.setPC 4412) true
      return result.charge (21 * pairs + 12) (2 * pairs + 1))] at run
  exact run

private theorem fused_load_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.LD destination source offset) =
      (execInstrBr state (.LD destination source offset)).setPC (pc + 4) := by
  cases destination <;> rfl

private theorem fused_store_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.SD destination source offset) =
      (execInstrBr state (.SD destination source offset)).setPC (pc + 4) := rfl

private theorem fused_root_pc (state : MachineState) (pc : Word) :
    commitCopyState (state.setPC pc) 79 = (commitCopyState state 79).setPC (pc + 32) := by
  rw [commit_copy_expansion, commit_copy_expansion]
  simp only [show (79 : Nat) ≠ 46 by decide, show (79 : Nat) ≠ 55 by decide,
    ite_false, ite_true, List.foldl, fused_load_pc, fused_store_pc]
  simp only [BitVec.add_assoc]
  rfl

/-- Both parent exit paths have already paid their jump. Root copy and halt cost eleven. -/
theorem fused_root (state : MachineState) (messageBase : Word)
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (11 + fuel)
      ((cursorBaseFrame state messageBase).setPC 4412) true =
      pure ⟨.success, cursorBaseFrame (commitExitState (commitCopyState state 79)) messageBase, 11, 0⟩ := by
  rw [commit_root ((cursorBaseFrame state messageBase).setPC 4412) rfl rootValid outputValid]
  rw [cursor_base_pc, cursor_base_root_copy, cursor_base_exit, fused_root_pc]
  rw [cursor_exit_pc]

/-- For even count=2*pairs+2, exact post-random cost is 36*count+7*pairs+23
instructions and 92*count+21*pairs+30 cycles. The zero-parent case is separate. -/
theorem fused_body (callFetched : CommitLeafCallFetched)
    (saltFetched : CursorSaltFetched (submission.image .commit))
    (prefixFetched : CursorPrefixFetched (submission.image .commit))
    (tailFetched : FusedTailFetched (submission.image .commit))
    (latchFetched : FusedLatchFetched (submission.image .commit))
    (exitFetched : FusedExitFetched (submission.image .commit))
    (parentFetched : FusedParentFetched (submission.image .commit))
    (state : MachineState) (count pairs : Nat) (messageBase : Word)
    (evenCount : count = 2 * pairs + 2) (bounded : count ≤ 2 ^ 24)
    (leaves : CommitLeavesInvariant state count)
    (heapWindow : (state.getReg .x23).toNat + 32 * count = (state.getReg .x22).toNat)
    (total : state.getReg .x19 = BitVec.ofNat 64 count)
    (parents : ParentBuffers (state.getReg .x9) (count - 1))
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (36 * count + 7 * pairs + 23 + fuel)
      (cursorLeafFrame state messageBase) true =
      (do let finished ← commitBody state count
          return ⟨.success, cursorBaseFrame finished messageBase,
            92 * count + 21 * pairs + 30, 9 * count - 1⟩) := by
  have nonzero : count ≠ 0 := by omega
  have residualCount : count - 1 = 2 * pairs + 1 := by omega
  have initialPC : state.pc = 4280 := by simpa [nonzero] using leaves.pc
  have leavesRun := fused_leaves callFetched saltFetched prefixFetched tailFetched latchFetched
    state count messageBase leaves heapWindow (7 + (7 * pairs + 5 + (11 + fuel)))
  simp only [if_neg nonzero] at leavesRun
  rw [← initialPC, fused_normalize_self_pc] at leavesRun
  rw [show 36 * count + 7 * pairs + 23 + fuel =
      36 * count + (7 + (7 * pairs + 5 + (11 + fuel))) by omega, leavesRun]
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
  have parentRun := fused_parents_execute parentFetched ready pairs messageBase
    (by omega) (commit_parents_start_pc hashed nonempty)
    (by rw [← residualCount]; exact readyPointers)
    (commit_parents_start_constants hashed leafInvariant.oracleReady)
    (by rw [← residualCount]; exact readyBuffers) (11 + fuel)
  dsimp only [ready] at parentRun
  rw [fused_parent_setup exitFetched hashed messageBase leafDone.1 nonempty, parentRun]
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
