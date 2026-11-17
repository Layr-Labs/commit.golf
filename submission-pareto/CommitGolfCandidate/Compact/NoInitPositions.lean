import CommitGolfCandidate.Compact.NoInitPosition

/-! The complete unrolled opening loop preserves the original position-state
sequence. Only its final physical PC and its exact instruction cost change. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute openingPositionState

private theorem noInit_address_add (address : Word) (offset : Nat)
    (bounded : address.toNat+offset≤MEMORY_BYTES) :
    (address+BitVec.ofNat 64 offset).toNat=address.toNat+offset := by
  have small : address.toNat+offset<2^64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : offset<2^64),
    Nat.mod_eq_of_lt small]

theorem noInit_positions_loop (remaining : Nat) (bounded : remaining ≤ LENGTH)
    (state : MachineState) (counter : state.getReg .x27 = BitVec.ofNat 64 remaining)
    (pc : state.pc = if remaining=0 then 5508 else 4176)
    (counterZero : state.getReg .x28=0)
    (indices : ∀ offset < remaining,
      (state.getMem (state.getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24)
    (indexSpace : (state.getReg .x24).toNat + 8 * remaining ≤ (state.getReg .x25).toNat)
    (indexAligned : (state.getReg .x24).toNat % 8 = 0)
    (leaves : state.getReg .x19 = 16777216)
    (saltBound : (state.getReg .x18).toNat + 2 ^ 29 ≤ MEMORY_BYTES)
    (saltAligned : (state.getReg .x18).toNat % 8 = 0)
    (heapBound : (state.getReg .x9).toNat + 2 ^ 30 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (outputBound : (state.getReg .x25).toNat + 792 * remaining ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute noInitImage (330 * remaining + fuel) state allowCoins =
      (do let result ← execute noInitImage fuel
            ((openingPositionState^[remaining] state).setPC 5508) allowCoins
          return result.charge (330 * remaining) 0) := by
  induction remaining generalizing state with
  | zero =>
    have same : state.setPC (5508 : Word)=state := by
      have h : state.pc=5508 := by simpa using pc
      rw [←h]
      cases state
      rfl
    simp [Execution.charge]
    exact congrArg (fun current => execute noInitImage fuel current allowCoins) same.symm
  | succ remaining ih =>
    have small : remaining < 2 ^ 64 := by
      norm_num [LENGTH, LOG_LENGTH] at bounded
      omega
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingPositionState state).getReg .x27 = BitVec.ofNat 64 remaining := by
      rw [(opening_position_progress state).2.2.1, counter, subtract]
    have nextPC : 0 < remaining → (openingPositionState state).pc = 4176 := by
      intro positive
      rw [noInit_position_pc, counter, subtract, if_neg]
      intro noInit
      have equal := congrArg BitVec.toNat noInit
      change remaining % 2 ^ 64 = 0 at equal
      rw [Nat.mod_eq_of_lt small] at equal
      omega
    have nextIndex : ((openingPositionState state).getReg .x24).toNat =
        (state.getReg .x24).toNat + 8 := by
      rw [(opening_position_progress state).1]
      exact noInit_address_add (state.getReg .x24) 8 (by omega)
    have nextOutput : ((openingPositionState state).getReg .x25).toNat =
        (state.getReg .x25).toNat + 792 := by
      rw [(opening_position_progress state).2.1]
      exact noInit_address_add (state.getReg .x25) 792 (by omega)
    have nextIndices : ∀ offset < remaining,
        ((openingPositionState state).getMem
          ((openingPositionState state).getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24 := by
      intro offset offsetBound
      have address : (openingPositionState state).getReg .x24 + BitVec.ofNat 64 (8 * offset) =
          state.getReg .x24 + BitVec.ofNat 64 (8 * (offset + 1)) := by
        rw [(opening_position_progress state).1]
        simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
        rw [BitVec.add_comm (8 : Word)]
        rfl
      rw [address, opening_position_memory_below]
      · exact indices (offset + 1) (by omega)
      · omega
      · rw [noInit_address_add _ _ (by omega)]
        omega
    have indexValid : accessValid (state.getReg .x24) 8 = true := by
      simp only [accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, indexAligned⟩
    have indexBound : (state.getMem (state.getReg .x24)).toNat < 2 ^ 24 := by
      simpa using indices 0 (by omega)
    have nextBases := opening_position_bases state
    have sourcePC : state.pc=4176 := by simpa using pc
    have run := noInit_position state sourcePC counterZero indexValid indexBound leaves
      saltBound saltAligned heapBound heapAligned (by omega) outputAligned
      (330*remaining+fuel) allowCoins
    rw [counter,subtract] at run
    by_cases last : remaining=0
    · subst remaining
      rw [show 330*(0+1)+fuel=330+(330*0+fuel) by omega,run]
      simp [Execution.charge]
    · have nonnoInit : BitVec.ofNat 64 remaining≠(0 : Word) := by
        intro noInit
        have equal := congrArg BitVec.toNat noInit
        change remaining%2^64=0 at equal
        rw [Nat.mod_eq_of_lt small] at equal
        omega
      have oldPC : (openingPositionState state).pc=4176 := nextPC (by omega)
      have same : (openingPositionState state).setPC (4176 : Word)=openingPositionState state := by
        rw [←oldPC]
        generalize openingPositionState state=finished
        cases finished
        rfl
      rw [if_neg nonnoInit,same] at run
      rw [show 330*(remaining+1)+fuel=330+(330*remaining+fuel) by omega,run,
        ih (by omega) (openingPositionState state) nextCounter
          (by simpa [last] using oldPC) (noInit_position_counter state) nextIndices
          (by rw [nextIndex,nextOutput];omega) (by rw [nextIndex];omega)
          (by simpa only [nextBases.2.2] using leaves)
          (by simpa only [nextBases.2.1] using saltBound)
          (by simpa only [nextBases.2.1] using saltAligned)
          (by simpa only [nextBases.1] using heapBound)
          (by simpa only [nextBases.1] using heapAligned)
          (by rw [nextOutput];omega) (by rw [nextOutput];omega)]
      simp [Function.iterate_succ_apply,Execution.charge,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end CommitGolfCandidate.Compact
