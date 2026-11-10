import CommitGolfCandidate.CapCheckRootOutcome
import CommitGolfCandidate.CapCheckExit

/-! Final four-word comparison execution, including the actual jump to the
success epilogue and immediate rejection after the first unequal word. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_root_loop_pc (state : MachineState) (word count : Nat)
    (bounded : word+count ≤ 4)
    (pc : state.pc = BitVec.ofNat 64 (4740+12*word)) :
    (capCheckRootLoop state word count).1.pc =
      if (capCheckRootLoop state word count).2 then
        BitVec.ofNat 64 (4740+12*(word+count)) else 4808 := by
  induction count generalizing state word with
  | zero => simpa only [capCheckRootLoop, ↓reduceIte, Nat.add_zero] using pc
  | succ count ih =>
    by_cases equal : CapCheckRootEqual state word
    · have nextPC : (capCheckRootPrefix state word 3).pc =
          BitVec.ofNat 64 (4740+12*(word+1)) := by
        rw [cap_check_root_exit state word (by omega) pc, if_pos equal]
        congr 1
        omega
      rw [capCheckRootLoop, if_pos equal]
      have tail := ih (capCheckRootPrefix state word 3) (word+1)
        (by omega) nextPC
      simpa only [Nat.add_assoc, Nat.add_comm 1 count] using tail
    · rw [capCheckRootLoop, if_neg equal]
      exact (cap_check_root_exit state word (by omega) pc).trans
        (by simp only [if_neg equal, Bool.false_eq_true, ↓reduceIte])

theorem cap_check_root_steps_passed (state : MachineState) (word count : Nat)
    (passed : (capCheckRootLoop state word count).2 = true) :
    capCheckRootSteps state word count = 3*count := by
  induction count generalizing state word with
  | zero => rfl
  | succ count ih =>
    by_cases equal : CapCheckRootEqual state word
    · simp only [capCheckRootLoop, if_pos equal] at passed
      rw [capCheckRootSteps, if_pos equal, ih _ _ passed]
      omega
    · simp only [capCheckRootLoop, if_neg equal] at passed
      contradiction

def capCheckRootDone (state : MachineState) : MachineState :=
  capFlowState (.jump 8) (capCheckRootLoop state 0 4).1

theorem cap_check_root_done_pc (state : MachineState) (pc : state.pc = 4740)
    (passed : (capCheckRootLoop state 0 4).2 = true) :
    (capCheckRootDone state).pc = 4796 := by
  rw [capCheckRootDone, cap_flow_jump_pc,
    cap_check_root_loop_pc state 0 4 (by decide) pc, passed]
  rfl

theorem cap_check_root_pass_execute (state : MachineState) (pc : state.pc = 4740)
    (passed : (capCheckRootLoop state 0 4).2 = true)
    (scratchValid : ∀ i < 4, accessValid
      (state.getReg .x18+signExtend12 (BitVec.ofNat 12 (32+8*i))) 8 = true)
    (rootValid : ∀ i < 4, accessValid
      (state.getReg .x26+signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (13+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckRootDone state) allowCoins
          return result.charge 13 0) := by
  have steps := cap_check_root_steps_passed state 0 4 passed
  have endPC : (capCheckRootLoop state 0 4).1.pc = 4788 := by
    rw [cap_check_root_loop_pc state 0 4 (by decide) pc, passed]
    rfl
  have fetched : fetch ((capExperimental 24).image .check)
      (capCheckRootLoop state 0 4).1 =
      some (.base (capFlowInstruction (.jump 8))) := by
    apply cap_image_fetch _ _ 173 _ (by decide) endPC
    rfl
  rw [show 13+fuel = capCheckRootSteps state 0 4+(1+fuel) by omega,
    cap_check_root_loop_execute state 0 4 (by decide) (fun _ => pc)
      scratchValid rootValid, cap_flow_execute _ (.jump 8) _ fetched, steps]
  simp [capCheckRootDone, bind_assoc, Execution.charge, ← Nat.add_assoc]

theorem cap_check_root_fail_execute (state : MachineState) (pc : state.pc = 4740)
    (failed : (capCheckRootLoop state 0 4).2 = false)
    (scratchValid : ∀ i < 4, accessValid
      (state.getReg .x18+signExtend12 (BitVec.ofNat 12 (32+8*i))) 8 = true)
    (rootValid : ∀ i < 4, accessValid
      (state.getReg .x26+signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check)
      (capCheckRootSteps state 0 4+3+fuel) state allowCoins =
      pure ⟨.failure, capCheckExitState (capCheckRootLoop state 0 4).1 false,
        capCheckRootSteps state 0 4+3, 0⟩ := by
  have endPC : (capCheckRootLoop state 0 4).1.pc = 4808 := by
    rw [cap_check_root_loop_pc state 0 4 (by decide) pc, failed]
    rfl
  rw [Nat.add_assoc, cap_check_root_loop_execute state 0 4
    (by decide) (fun _ => pc) scratchValid rootValid]
  change (do
    let result ← execute (capWalkImage true) (3+fuel)
      (capCheckRootLoop state 0 4).1 allowCoins
    return result.charge (capCheckRootSteps state 0 4) 0) = _
  rw [cap_check_exit _ false endPC]
  simp [Execution.charge, Nat.add_comm]

end CommitGolfCandidate
