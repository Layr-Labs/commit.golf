import CommitGolfCandidate.CapCheckDuplicateOutcome
import CommitGolfCandidate.CapCheckExit

/-! Exact completion of the four-word comparison. Successful comparisons take
the actual jump over the first-occurrence store; a mismatch reaches the real
three-instruction rejection epilogue without reading subsequent words. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_duplicate_loop_pc (state : MachineState) (word count : Nat)
    (bounded : word+count ≤ 4)
    (pc : state.pc = BitVec.ofNat 64 (4448+12*word)) :
    (capCheckDuplicateLoop state word count).1.pc =
      if (capCheckDuplicateLoop state word count).2 then
        BitVec.ofNat 64 (4448+12*(word+count)) else 4808 := by
  induction count generalizing state word with
  | zero => simpa only [capCheckDuplicateLoop, ↓reduceIte, Nat.add_zero] using pc
  | succ count ih =>
    by_cases equal : CapCheckDuplicateEqual state word
    · have nextPC : (capCheckDuplicatePrefix state word 3).pc =
          BitVec.ofNat 64 (4448+12*(word+1)) := by
        rw [cap_check_duplicate_exit state word (by omega) pc, if_pos equal]
        congr 1
        omega
      rw [capCheckDuplicateLoop, if_pos equal]
      have tail := ih (capCheckDuplicatePrefix state word 3) (word+1)
        (by omega) nextPC
      simpa only [Nat.add_assoc, Nat.add_comm 1 count] using tail
    · rw [capCheckDuplicateLoop, if_neg equal]
      exact (cap_check_duplicate_exit state word (by omega) pc).trans
        (by simp only [if_neg equal, Bool.false_eq_true, ↓reduceIte])

theorem cap_check_duplicate_steps_passed (state : MachineState) (word count : Nat)
    (passed : (capCheckDuplicateLoop state word count).2 = true) :
    capCheckDuplicateSteps state word count = 3*count := by
  induction count generalizing state word with
  | zero => rfl
  | succ count ih =>
    by_cases equal : CapCheckDuplicateEqual state word
    · simp only [capCheckDuplicateLoop, if_pos equal] at passed
      rw [capCheckDuplicateSteps, if_pos equal, ih _ _ passed]
      omega
    · simp only [capCheckDuplicateLoop, if_neg equal] at passed
      contradiction

def capCheckDuplicateDone (state : MachineState) : MachineState :=
  capFlowState (.jump 40) (capCheckDuplicateLoop state 0 4).1

theorem cap_check_duplicate_done_pc (state : MachineState) (pc : state.pc = 4448)
    (passed : (capCheckDuplicateLoop state 0 4).2 = true) :
    (capCheckDuplicateDone state).pc = 4536 := by
  rw [capCheckDuplicateDone, cap_flow_jump_pc,
    cap_check_duplicate_loop_pc state 0 4 (by decide) pc, passed]
  rfl

theorem cap_check_duplicate_pass_execute (state : MachineState) (pc : state.pc = 4448)
    (passed : (capCheckDuplicateLoop state 0 4).2 = true)
    (scratchValid : ∀ i < 4, accessValid
      (state.getReg .x21+signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (rootValid : ∀ i < 4, accessValid
      (state.getReg .x23+signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (13+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckDuplicateDone state) allowCoins
          return result.charge 13 0) := by
  have steps := cap_check_duplicate_steps_passed state 0 4 passed
  have endPC : (capCheckDuplicateLoop state 0 4).1.pc = 4496 := by
    rw [cap_check_duplicate_loop_pc state 0 4 (by decide) pc, passed]
    rfl
  have fetched : fetch ((capExperimental 24).image .check)
      (capCheckDuplicateLoop state 0 4).1 =
      some (.base (capFlowInstruction (.jump 40))) := by
    apply cap_image_fetch _ _ 100 _ (by decide) endPC
    rfl
  rw [show 13+fuel = capCheckDuplicateSteps state 0 4+(1+fuel) by omega,
    cap_check_duplicate_loop_execute state 0 4 (by decide) (fun _ => pc)
      scratchValid rootValid, cap_flow_execute _ (.jump 40) _ fetched, steps]
  simp [capCheckDuplicateDone, bind_assoc, Execution.charge, ← Nat.add_assoc]

theorem cap_check_duplicate_fail_execute (state : MachineState) (pc : state.pc = 4448)
    (failed : (capCheckDuplicateLoop state 0 4).2 = false)
    (scratchValid : ∀ i < 4, accessValid
      (state.getReg .x21+signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (rootValid : ∀ i < 4, accessValid
      (state.getReg .x23+signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check)
      (capCheckDuplicateSteps state 0 4+3+fuel) state allowCoins =
      pure ⟨.failure, capCheckExitState (capCheckDuplicateLoop state 0 4).1 false,
        capCheckDuplicateSteps state 0 4+3, 0⟩ := by
  have endPC : (capCheckDuplicateLoop state 0 4).1.pc = 4808 := by
    rw [cap_check_duplicate_loop_pc state 0 4 (by decide) pc, failed]
    rfl
  rw [Nat.add_assoc, cap_check_duplicate_loop_execute state 0 4
    (by decide) (fun _ => pc) scratchValid rootValid]
  change (do
    let result ← execute (capWalkImage true) (3+fuel)
      (capCheckDuplicateLoop state 0 4).1 allowCoins
    return result.charge (capCheckDuplicateSteps state 0 4) 0) = _
  rw [cap_check_exit _ false endPC]
  simp [Execution.charge, Nat.add_comm]

end CommitGolfCandidate
