import CommitGolfCandidate.CapCheckRootEffect

/-! At most four final commitment words are compared. The deterministic
loop stops at the first mismatch and retains its exact early-exit cost. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckRootLoop (state : MachineState) (word : Nat) :
    Nat → MachineState × Bool
  | 0 => (state,true)
  | remaining+1 =>
      let next := capCheckRootPrefix state word 3
      if CapCheckRootEqual state word then
        capCheckRootLoop next (word+1) remaining
      else (next,false)

def capCheckRootSteps (state : MachineState) (word : Nat) : Nat → Nat
  | 0 => 0
  | remaining+1 =>
      if CapCheckRootEqual state word then
        3+capCheckRootSteps (capCheckRootPrefix state word 3) (word+1) remaining
      else 3

theorem cap_check_root_steps_bound (state : MachineState) (word count : Nat) :
    capCheckRootSteps state word count ≤ 3*count := by
  induction count generalizing state word with
  | zero => rfl
  | succ count ih =>
    unfold capCheckRootSteps
    split
    · have tail := ih (capCheckRootPrefix state word 3) (word+1)
      omega
    · omega

theorem cap_check_root_loop_execute (state : MachineState) (word count : Nat)
    (bounded : word+count ≤ 4)
    (pc : 0 < count → state.pc = BitVec.ofNat 64 (4740+12*word))
    (scratchValid : ∀ i < 4, accessValid
      (state.getReg .x18 + signExtend12 (BitVec.ofNat 12 (32+8*i))) 8 = true)
    (rootValid : ∀ i < 4, accessValid
      (state.getReg .x26 + signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check)
      (capCheckRootSteps state word count+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckRootLoop state word count).1 allowCoins
          return result.charge (capCheckRootSteps state word count) 0) := by
  induction count generalizing state word with
  | zero =>
    simp only [capCheckRootSteps, capCheckRootLoop, Nat.zero_add]
    simp [Execution.charge]
  | succ count ih =>
    let next := capCheckRootPrefix state word 3
    have nextScratch (i : Nat) (inside : i < 4) :
        accessValid (next.getReg .x18 +
          signExtend12 (BitVec.ofNat 12 (32+8*i))) 8 = true := by
      rw [cap_check_root_register state word .x18 (by decide) (by decide)]
      exact scratchValid i inside
    have nextRoot (i : Nat) (inside : i < 4) :
        accessValid (next.getReg .x26 +
          signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true := by
      rw [cap_check_root_register state word .x26 (by decide) (by decide)]
      exact rootValid i inside
    by_cases equal : CapCheckRootEqual state word
    · have nextPC (positive : 0 < count) :
          next.pc = BitVec.ofNat 64 (4740+12*(word+1)) := by
        rw [cap_check_root_exit state word (by omega) (pc (by omega)),
          if_pos equal]
        congr 1
        omega
      simp only [capCheckRootSteps, capCheckRootLoop, if_pos equal]
      rw [Nat.add_assoc,
        cap_check_root_execute state word (by omega) (pc (by omega))
          (scratchValid word (by omega)) (rootValid word (by omega)),
        ih next (word+1) (by omega) nextPC nextScratch nextRoot]
      simp [Execution.charge, ← Nat.add_assoc]
      rfl
    · simp only [capCheckRootSteps, capCheckRootLoop, if_neg equal]
      exact cap_check_root_execute state word (by omega) (pc (by omega))
        (scratchValid word (by omega)) (rootValid word (by omega)) fuel allowCoins

theorem cap_check_root_loop_memory (state : MachineState) (word count : Nat) :
    (capCheckRootLoop state word count).1.mem = state.mem := by
  induction count generalizing state word with
  | zero => rfl
  | succ count ih =>
    unfold capCheckRootLoop
    split
    · exact (ih _ _).trans (cap_check_root_memory state word)
    · exact cap_check_root_memory state word

end CommitGolfCandidate
