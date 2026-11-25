import CommitGolfCandidate.FusedPosition

/-! Whole leaf-loop composition retains the old virtual source progress for
refinement, while physical execution uses only the carried x10 and heap latch. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute commitPositionRun

theorem fused_normalize_self_pc (state : MachineState) (messageBase : Word) :
    cursorNormalize state messageBase state.pc = cursorLeafFrame state messageBase := by
  cases state
  rfl

/-- Natural reference progress proves all memory accesses and heap-end branches.
The real repeated cost is 36 instructions and 92 cycles per committed leaf. -/
theorem fused_leaves (saltFetched : CursorSaltFetched (submission.image .commit))
    (prefixFetched : CursorPrefixFetched (submission.image .commit))
    (tailFetched : FusedTailFetched (submission.image .commit))
    (latchFetched : FusedLatchFetched (submission.image .commit))
    (callFetched : ∀ state : MachineState, state.pc = 4312 →
      fetch (submission.image .commit) state = some (.base (.JAL .x1 144)))
    (state : MachineState) (remaining : Nat) (messageBase : Word)
    (invariant : CommitLeavesInvariant state remaining)
    (window : (state.getReg .x23).toNat + 32 * remaining = (state.getReg .x22).toNat)
    (fuel : Nat) :
    execute (submission.image .commit) (36 * remaining + fuel)
      (cursorNormalize state messageBase (if remaining = 0 then 4564 else 4280)) true =
      (do let finished ← commitLeaves state remaining
          let result ← execute (submission.image .commit) fuel
            (cursorNormalize finished messageBase 4564) true
          return result.charge (92 * remaining) (8 * remaining)) := by
  induction remaining generalizing state with
  | zero => simp [commitLeaves, Execution.charge]
  | succ remaining ih =>
    have pc : state.pc = 4280 := by simpa using invariant.pc
    simp only [show remaining + 1 ≠ 0 by omega, ite_false]
    rw [← pc, fused_normalize_self_pc,
      show 36 * (remaining + 1) + fuel = 36 + (36 * remaining + fuel) by omega,
      fused_position saltFetched prefixFetched tailFetched latchFetched callFetched state messageBase pc
        invariant.scratch invariant.sourceAbove invariant.oracleReady
        (fun word => invariant.salts word.val (by omega))
        (fun word => invariant.heap word.val (by omega))
        (fun word bound => invariant.message word (by omega))
        remaining window]
    simp only [commitLeaves, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (commit_leaves_next_invariant state next remaining invariant reached)
      (outer_heap_progress_next state next remaining window reached)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end CommitGolfCandidate
