import CommitGolfCandidate.CapCheckDuplicateEffect

/-! At most four duplicate words are compared. The deterministic loop stops
at the first mismatch; its exact fuel/cycles retain that early-exit schedule,
rather than assuming all four words were inspected on rejected inputs. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckDuplicateLoop (state : MachineState) (word : Nat) :
    Nat → MachineState × Bool
  | 0 => (state,true)
  | remaining+1 =>
      let next := capCheckDuplicatePrefix state word 3
      if CapCheckDuplicateEqual state word then
        capCheckDuplicateLoop next (word+1) remaining
      else (next,false)

def capCheckDuplicateSteps (state : MachineState) (word : Nat) : Nat → Nat
  | 0 => 0
  | remaining+1 =>
      if CapCheckDuplicateEqual state word then
        3+capCheckDuplicateSteps (capCheckDuplicatePrefix state word 3) (word+1) remaining
      else 3

theorem cap_check_duplicate_steps_bound (state : MachineState) (word count : Nat) :
    capCheckDuplicateSteps state word count ≤ 3*count := by
  induction count generalizing state word with
  | zero => rfl
  | succ count ih =>
    unfold capCheckDuplicateSteps
    split
    · have tail := ih (capCheckDuplicatePrefix state word 3) (word+1)
      omega
    · omega

theorem cap_check_duplicate_loop_execute (state : MachineState) (word count : Nat)
    (bounded : word+count ≤ 4)
    (pc : 0 < count → state.pc = BitVec.ofNat 64 (4448+12*word))
    (scratchValid : ∀ i < 4, accessValid
      (state.getReg .x21 + signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (rootValid : ∀ i < 4, accessValid
      (state.getReg .x23 + signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check)
      (capCheckDuplicateSteps state word count+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckDuplicateLoop state word count).1 allowCoins
          return result.charge (capCheckDuplicateSteps state word count) 0) := by
  induction count generalizing state word with
  | zero =>
    simp only [capCheckDuplicateSteps, capCheckDuplicateLoop, Nat.zero_add]
    simp [Execution.charge]
  | succ count ih =>
    let next := capCheckDuplicatePrefix state word 3
    have nextScratch (i : Nat) (inside : i < 4) :
        accessValid (next.getReg .x21 +
          signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true := by
      rw [cap_check_duplicate_register state word .x21 (by decide) (by decide)]
      exact scratchValid i inside
    have nextRoot (i : Nat) (inside : i < 4) :
        accessValid (next.getReg .x23 +
          signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true := by
      rw [cap_check_duplicate_register state word .x23 (by decide) (by decide)]
      exact rootValid i inside
    by_cases equal : CapCheckDuplicateEqual state word
    · have nextPC (positive : 0 < count) :
          next.pc = BitVec.ofNat 64 (4448+12*(word+1)) := by
        rw [cap_check_duplicate_exit state word (by omega) (pc (by omega)),
          if_pos equal]
        congr 1
        omega
      simp only [capCheckDuplicateSteps, capCheckDuplicateLoop, if_pos equal]
      rw [Nat.add_assoc,
        cap_check_duplicate_execute state word (by omega) (pc (by omega))
          (scratchValid word (by omega)) (rootValid word (by omega)),
        ih next (word+1) (by omega) nextPC nextScratch nextRoot]
      simp [Execution.charge, ← Nat.add_assoc]
      rfl
    · simp only [capCheckDuplicateSteps, capCheckDuplicateLoop, if_neg equal]
      exact cap_check_duplicate_execute state word (by omega) (pc (by omega))
        (scratchValid word (by omega)) (rootValid word (by omega)) fuel allowCoins

theorem cap_check_duplicate_loop_memory (state : MachineState) (word count : Nat) :
    (capCheckDuplicateLoop state word count).1.mem = state.mem := by
  induction count generalizing state word with
  | zero => rfl
  | succ count ih =>
    unfold capCheckDuplicateLoop
    split
    · exact (ih _ _).trans (cap_check_duplicate_memory state word)
    · exact cap_check_duplicate_memory state word

end CommitGolfCandidate
