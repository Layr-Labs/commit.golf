import CommitGolfCandidate.CapOpenReadDigest

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_boundary_increment_length (marked : Nat → Bool) (control : CapDfsControl) :
    capBoundaryIncrement marked control = 32 * (capControlBoundaryHead marked control).length := by
  cases control <;> simp only [capBoundaryIncrement, capControlBoundaryHead,
    List.length_nil, Nat.mul_zero]
  split <;> simp

theorem cap_open_run_cursor_count (marked : Nat → Bool) (count : Nat)
    (control : CapDfsControl) (state final : MachineState) (cursor : Nat)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (reached : final ∈ support (capDfsRun false marked count control state)) :
    final.getReg .x25 =
      BitVec.ofNat 64 (cursor + 32 * (capControlBoundaries marked count control).length) := by
  induction count generalizing control state cursor with
  | zero =>
      have same := eq_of_mem_support_pure state reached
      subst final
      simpa only [capControlBoundaries, List.length_nil, Nat.mul_zero, Nat.add_zero] using pointer
  | succ count ih =>
      rw [capDfsRun] at reached
      obtain ⟨next, first, tail⟩ := mem_support_bind_peel _ _ reached
      have nextPointer := cap_dfs_open_cursor_effect marked control state next cursor pointer first
      have finished := ih (capControlStep marked control) next
        (cursor + capBoundaryIncrement marked control) nextPointer tail
      rw [finished]
      congr 1
      rw [capControlBoundaries, List.length_append, cap_boundary_increment_length]
      omega

theorem cap_open_query_total_zero (marked : Nat → Bool) (count : Nat)
    (control : CapDfsControl) :
    capDfsQueryTotal false marked count control = 0 := by
  induction count generalizing control with
  | zero => rfl
  | succ count ih =>
      rw [capDfsQueryTotal, ih]
      cases control <;> simp only [capDfsStepQueries, Nat.add_zero]
      split <;> simp

theorem cap_open_root_cursor_count (marked : Nat → Bool)
    (state final : MachineState) (cursor : Nat)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (reached : final ∈ support (capDfsRun false marked 1022 (.visit 1) state)) :
    final.getReg .x25 =
      BitVec.ofNat 64 (cursor + 32 * (capSubtreeBoundaries marked 8 1).length) := by
  simpa only [cap_root_boundary_order] using
    cap_open_run_cursor_count marked 1022 (.visit 1) state final cursor pointer reached

end CommitGolfCandidate
