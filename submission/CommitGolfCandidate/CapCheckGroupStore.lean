import CommitGolfCandidate.CapCheckGroupBranch
import CommitGolfCandidate.CapWordCopy

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckGroupStoreState (state : MachineState) : MachineState :=
  execInstrBr (capWordCopyPrefix .x21 .x23 0 0 state 8) (.SD .x30 .x31 0)

theorem cap_check_group_store_copy_fetched :
    CapWordCopyFetched ((capExperimental 24).image .check) .x21 .x23 0 0 4500 := by
  intro state i bounded pc
  apply cap_image_fetch _ _ (101+i) _ (by omega)
  · rw [cap_word_copy_prefix_pc _ _ _ _ _ i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem store_charge (computation : OracleComp World Execution) :
    (do let result ← (do let result ← computation; return result.charge 1 0)
        return result.charge 8 0) =
      (do let result ← computation; return result.charge 9 0) := by
  simp [bind_assoc, Execution.charge, ← Nat.add_assoc]

attribute [local irreducible] execute capCheckGroupStoreState

theorem cap_check_group_store_execute (state : MachineState)
    (pc : state.pc = 4500)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x21 +
        signExtend12 (BitVec.ofNat 12 (8*word.val))) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 +
        signExtend12 (BitVec.ofNat 12 (8*word.val))) 8 = true)
    (markValid : accessValid (state.getReg .x30) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (9+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckGroupStoreState state) allowCoins
          return result.charge 9 0) := by
  let copied := capWordCopyPrefix .x21 .x23 0 0 state 8
  have copiedPC : copied.pc = 4532 := by
    rw [cap_word_copy_prefix_pc _ _ _ _ _ 8 (by decide), pc]
    rfl
  have copiedMark := cap_word_copy_prefix_register .x21 .x23 0 0 state 8
    (by decide) .x30 (by decide)
  have fetched : fetch ((capExperimental 24).image .check) copied =
      some (.base (.SD .x30 .x31 0)) := by
    apply cap_image_fetch _ copied 109 _ (by decide) copiedPC
    rfl
  have stepped : ordinaryStep copied (.base (.SD .x30 .x31 0)) =
      some (capCheckGroupStoreState state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess]
    change (if accessValid (copied.getReg .x30 + (0#64)) 8 = true then
      some (execInstrBr copied (.SD .x30 .x31 0)) else none) = _
    rw [BitVec.add_zero, copiedMark, markValid]
    unfold capCheckGroupStoreState
    rfl
  rw [show 9+fuel = 8+(1+fuel) by omega,
    cap_word_copy_execute _ .x21 .x23 0 0 4500
      cap_check_group_store_copy_fetched state pc (by decide) (by decide)
      (by simpa only [Nat.zero_add] using sourceValid)
      (by simpa only [Nat.zero_add] using destinationValid)]
  change (do
    let result ← execute ((capExperimental 24).image .check) (1+fuel) copied allowCoins
    return result.charge 8 0) = _
  rw [Nat.add_comm 1 fuel,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  exact store_charge _

end CommitGolfCandidate
