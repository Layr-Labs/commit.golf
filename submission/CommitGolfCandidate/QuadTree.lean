import CommitGolfCandidate.ContiguousTree
import CommitGolfCandidate.QuadParents

/-! The contiguous leaves compose with the new four-parent grouping. Every
query and heap write follows the retained reference tree; only branch sharing
changes the exact operational instruction and cycle counts. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute commitBody

/-- For count=4*groups+4, the exact post-random cost is
35*count+13*groups+32 instructions and 91*count+41*groups+53 cycles.
The zero-parent and N=2 cases are outside this challenge specialization. -/
theorem quad_body (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (latchFetched : ContiguousLatchFetched (submission.image .commit))
    (entryFetched : ContiguousEntryFetched (submission.image .commit))
    (exitFetched : ContiguousExitFetched (submission.image .commit))
    (parentFetched : QuadParentFetched (submission.image .commit))
    (state : MachineState) (count groups : Nat) (messageBase : Word)
    (evenCount : count = 4 * groups + 4) (bounded : count ≤ 2 ^ 24)
    (leaves : CommitLeavesInvariant state count)
    (heapWindow : (state.getReg .x23).toNat + 32 * count = (state.getReg .x22).toNat)
    (total : state.getReg .x19 = BitVec.ofNat 64 count)
    (parents : ParentBuffers (state.getReg .x9) (count - 1))
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (35 * count + 13 * groups + 32 + fuel)
      (cursorLeafFrame state messageBase) true =
      (do let finished ← commitBody state count
          return ⟨.success, cursorBaseFrame finished messageBase,
            91 * count + 41 * groups + 53, 9 * count - 1⟩) := by
  have nonzero : count ≠ 0 := by omega
  have residualCount : count - 1 = 4 * groups + 3 := by omega
  have initialPC : state.pc = 4280 := by simpa [nonzero] using leaves.pc
  have linkedInvariant := contiguous_link_invariant state count 4316 leaves
  have linkedWindow : ((state.setReg .x1 4316).getReg .x23).toNat + 32 * count =
      ((state.setReg .x1 4316).getReg .x22).toNat := by
    simpa [MachineState.setReg, MachineState.getReg] using heapWindow
  have leavesRun := contiguous_leaves saltFetched prefixFetched tailFetched latchFetched
    (state.setReg .x1 4316) count messageBase linkedInvariant
    (by simp only [MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)])
    linkedWindow (7 + (13 * groups + 12 + (11 + fuel)))
  simp only [if_neg nonzero] at leavesRun
  have erased : commitLeaves (state.setReg .x1 4316) count = commitLeaves state count := by
    have positive := contiguous_positive_leaves state (count - 1) 4316 (state.setReg .x1 4316).pc
    rw [hoist_pc_self] at positive
    simpa only [show count - 1 + 1 = count by omega] using positive
  rw [erased] at leavesRun
  rw [show 35 * count + 13 * groups + 32 + fuel =
      2 + (35 * count + (7 + (13 * groups + 12 + (11 + fuel)))) by omega,
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
  have parentRun := quad_parents_execute parentFetched ready groups messageBase
    (by omega) (commit_parents_start_pc hashed nonempty)
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
