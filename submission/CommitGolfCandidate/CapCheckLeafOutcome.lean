import CommitGolfCandidate.CapCheckLeafFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckLeafBlockState

theorem cap_check_leaf_loop_source (state : MachineState) (count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (capCheckLeafLoop state count)) :
    finished.getReg .x8 = state.getReg .x8 + BitVec.ofNat 64 (32 * count) := by
  induction count generalizing state with
  | zero =>
      simp only [capCheckLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
      subst finished
      simp
  | succ count ih =>
      simp only [capCheckLeafLoop, mem_support_bind_iff] at reachable
      obtain ⟨answer, _, tail⟩ := reachable
      rw [ih _ tail, (cap_check_leaf_block_pointers state answer).1]
      rw [show 32 * (count + 1) = 32 + 32 * count by omega, BitVec.ofNat_add,
        BitVec.add_assoc]
      rfl

end CommitGolfCandidate
