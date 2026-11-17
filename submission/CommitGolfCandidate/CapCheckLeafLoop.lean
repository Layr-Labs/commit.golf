import CommitGolfCandidate.CapCheckLeafBlock

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

def capCheckLeafLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | remaining + 1 => do
      let answer ← capCheckScratchQuery (readBuffer (capCheckLeafCopyState state) 256 64)
      capCheckLeafLoop (capCheckLeafBlockState state answer) remaining

theorem cap_check_leaf_loop_execute (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (pc : 0 < count → state.pc = 4824) (counter : state.getReg .x28 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 4 * count,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (17 * count + fuel) state allowCoins =
      (do let finished ← capCheckLeafLoop state count
          let result ← execute ((capExperimental 24).image .check) fuel finished allowCoins
          return result.charge (24 * count) count) := by
  induction count generalizing state with
  | zero => simp [capCheckLeafLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextCounter (answer : BitVec 256) :
        (capCheckLeafBlockState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(cap_check_leaf_block_pointers state answer).2, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (capCheckLeafBlockState state answer).pc = 4824 := by
      rw [cap_check_leaf_block_pc state answer (pc (by omega))]
      have nonzero : state.getReg .x28 - 1 ≠ 0 := by
        rw [← (cap_check_leaf_block_pointers state answer).2, nextCounter]
        intro zero
        have := congrArg BitVec.toNat zero
        change count % 18446744073709551616 = 0 at this
        omega
      exact if_neg nonzero
    have nextValid (answer : BitVec 256) (word : Nat) (bound : word < 4 * count) :
        accessValid ((capCheckLeafBlockState state answer).getReg .x8 +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      have valid := sourceValid (word + 4) (by omega)
      rw [(cap_check_leaf_block_pointers state answer).1]
      have address : state.getReg .x8 + 32 + BitVec.ofNat 64 (8 * word) =
          state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 4)) := by
        rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [show 17 * (count + 1) + fuel = 17 + (17 * count + fuel) by omega,
      cap_check_leaf_block_execute state (pc (by omega)) scratch currentValid]
    simp only [capCheckLeafLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (capCheckScratchQuery (readBuffer (capCheckLeafCopyState state) 256 64)) >>= continuation)
    funext answer
    rw [ih _ (by omega) (nextPC answer) (nextCounter answer)
      ((cap_check_leaf_block_register state answer .x21 (by decide)).trans scratch) (nextValid answer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]


theorem cap_check_leaf_loop_finished (state : MachineState) (count : Nat)
    (bounded : count ≤ 8) (pc : 0 < count → state.pc = 4824)
    (counter : state.getReg .x28 = BitVec.ofNat 64 count) (finished : MachineState)
    (reachable : finished ∈ support (capCheckLeafLoop state count)) :
    finished.getReg .x28 = 0 ∧ finished.getReg .x1 = state.getReg .x1 ∧
      (0 < count → finished.pc = 4892) := by
  induction count generalizing state with
  | zero =>
      simp only [capCheckLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
      subst finished
      exact ⟨counter, rfl, by omega⟩
  | succ count ih =>
      simp only [capCheckLeafLoop, mem_support_bind_iff] at reachable
      obtain ⟨answer, _, reached⟩ := reachable
      have nextCounter :
          (capCheckLeafBlockState state answer).getReg .x28 = BitVec.ofNat 64 count := by
        rw [(cap_check_leaf_block_pointers state answer).2, counter]
        change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
        rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
        congr 1
      have nextPC (positive : 0 < count) : (capCheckLeafBlockState state answer).pc = 4824 := by
        rw [cap_check_leaf_block_pc state answer (pc (by omega))]
        apply if_neg
        rw [← (cap_check_leaf_block_pointers state answer).2, nextCounter]
        intro zero
        have := congrArg BitVec.toNat zero
        change count % 18446744073709551616 = 0 at this
        omega
      have remaining := ih _ (by omega) nextPC nextCounter reached
      refine ⟨remaining.1, remaining.2.1.trans
        (cap_check_leaf_block_register state answer .x1 (by decide)), ?_⟩
      intro _
      by_cases empty : count = 0
      · subst count
        simp only [capCheckLeafLoop, support_pure, Set.mem_singleton_iff] at reached
        subst finished
        rw [cap_check_leaf_block_pc state answer (pc (by omega)), counter]
        rfl
      · exact remaining.2.2 (by omega)

end CommitGolfCandidate
