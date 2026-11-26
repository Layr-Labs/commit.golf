import CommitGolfCandidate.CommitLoop

import CommitGolfCandidate.TruncLeafBlock

namespace CommitGolfCandidate.Trunc

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

set_option maxHeartbeats 1200000

theorem commit_leaves (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (fuel : Nat) :
    execute (submission.image .commit) (547 * remaining + fuel) state true =
      (do let finished ← commitLeaves state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (1443 * remaining) (128 * remaining)) := by
  induction remaining generalizing state with
  | zero => simp [commitLeaves, Execution.charge]
  | succ remaining ih =>
    have mem : MEMORY_BYTES = 2^36 := rfl
    have pc : state.pc = 4232 := by simpa using invariant.pc
    have hslotB := invariant.slotBound
    have hsaltB := invariant.saltBound
    have hsaltA := invariant.saltAligned
    have hheapB := invariant.heapBound
    have saltValid : ∀ word < 64,
        accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word)) 8 = true := by
      intro word hw
      have hwb : (state.getReg .x18).toNat + 8 * word ≤ MEMORY_BYTES :=
        Nat.le_trans (by clear * - hw; omega) hsaltB
      simp only [accessValid, rangeValid, word_add_toNat _ (8 * word) hwb,
        Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact Nat.le_trans (by clear * - hw; omega) hsaltB
      · clear * - hsaltA; omega
    have hstep := commit_block state pc invariant.r5 invariant.r11 invariant.r13
      (state.getReg .x10).toNat (word_ofNat_toNat _) invariant.slotAligned
      (Nat.le_trans (by clear * -; omega) hslotB) saltValid
      (state.getReg .x23).toNat (word_ofNat_toNat _) invariant.heapAligned
      (Nat.le_trans (by clear * -; omega) hheapB) (547 * remaining + fuel)
    rw [show 547 * (remaining + 1) + fuel = 547 + (547 * remaining + fuel) by clear * -; omega,
      hstep]
    simp only [commitLeaves, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (commit_leaves_next_invariant state next remaining invariant reached)]
    simp only [bind_assoc, pure_bind, charge_charge,
      show 1443 + 1443 * remaining = 1443 * (remaining + 1) by omega,
      show 128 + 128 * remaining = 128 * (remaining + 1) by omega]

end CommitGolfCandidate.Trunc
