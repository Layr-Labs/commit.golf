import CommitGolfCandidate.ContiguousPosition

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute commitPositionRun

theorem contiguous_normalize_self_pc (state : MachineState) (messageBase : Word) :
    cursorNormalize state messageBase state.pc = cursorLeafFrame state messageBase := by
  cases state
  rfl

theorem contiguous_leaves (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (latchFetched : ContiguousLatchFetched (submission.image .commit))
    (state : MachineState) (remaining : Nat) (messageBase : Word)
    (invariant : CommitLeavesInvariant state remaining)
    (link : state.getReg .x1 = 4316)
    (window : (state.getReg .x23).toNat + 32 * remaining = (state.getReg .x22).toNat)
    (fuel : Nat) :
    execute (submission.image .commit) (34 * remaining + fuel)
      (cursorNormalize state messageBase (if remaining = 0 then 4592 else 4456)) true =
      (do let finished ← commitLeaves state remaining
          let result ← execute (submission.image .commit) fuel
            (cursorNormalize finished messageBase 4592) true
          return result.charge (90 * remaining) (8 * remaining)) := by
  induction remaining generalizing state with
  | zero => simp [commitLeaves, Execution.charge]
  | succ remaining ih =>
    have pc : state.pc = 4280 := by simpa using invariant.pc
    simp only [show remaining + 1 ≠ 0 by omega, ite_false]
    rw [show 34 * (remaining + 1) + fuel = 34 + (34 * remaining + fuel) by omega,
      contiguous_position saltFetched prefixFetched tailFetched latchFetched state messageBase pc
        link invariant.scratch invariant.sourceAbove invariant.oracleReady
        (fun word => invariant.salts word.val (by omega))
        (fun word => invariant.heap word.val (by omega))
        (fun word bound => invariant.message word (by omega))
        remaining window]
    simp only [commitLeaves, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (commit_leaves_next_invariant state next remaining invariant reached)
      (contiguous_position_link state next reached) (outer_heap_progress_next state next remaining window reached)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end CommitGolfCandidate
