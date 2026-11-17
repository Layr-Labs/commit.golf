import CommitGolfCandidate.CapCheckGroupEffect
import CommitGolfCandidate.CapCheckGroupStoreFrame
import CommitGolfCandidate.CapCheckDuplicateDigest

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckGroupCompared (state : MachineState) : MachineState :=
  capCheckGroupBranchState (capCheckGroupStartPrefix state 6)

def capCheckGroupResult (state : MachineState) : MachineState × Bool :=
  let compared := capCheckGroupCompared state
  if (capCheckGroupStartPrefix state 6).getReg .x6 = 0 then
    (capCheckGroupStoreState compared,true)
  else if (capCheckDuplicateLoop compared 0 4).2 then
    (capCheckDuplicateDone compared,true)
  else (capCheckExitState (capCheckDuplicateLoop compared 0 4).1 false,false)

def capCheckGroupSteps (state : MachineState) : Nat :=
  let compared := capCheckGroupCompared state
  if (capCheckGroupStartPrefix state 6).getReg .x6 = 0 then 16
  else 7+capCheckDuplicateSteps compared 0 4+
    if (capCheckDuplicateLoop compared 0 4).2 then 1 else 3

private theorem group_charge (computation : OracleComp World Execution) (steps : Nat) :
    (do
      let result ← (do
        let result ← (do let result ← computation; return result.charge steps 0)
        return result.charge 1 0)
      return result.charge 6 0) =
      (do let result ← computation; return result.charge (steps+7) 0) := by
  simp [Execution.charge, ← Nat.add_assoc]
  congr 1
  funext result
  congr 1
  omega

theorem cap_check_group_steps_bound (state : MachineState) :
    capCheckGroupSteps state ≤ 22 := by
  have bound := cap_check_duplicate_steps_bound (capCheckGroupCompared state) 0 4
  dsimp only [capCheckGroupSteps]
  split
  · omega
  · split <;> omega

attribute [local irreducible] capCheckGroupStartPrefix execute

theorem cap_check_group_run_execute (state : MachineState) (pc : state.pc = 4420)
    (markValid : accessValid ((capCheckGroupStartPrefix state 5).getReg .x30) 8 = true)
    (scratchValid : ∀ i < 4, accessValid
      (state.getReg .x21+signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (rootValid : ∀ i < 4, accessValid
      ((capCheckGroupStartPrefix state 6).getReg .x23+
        signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true)
    (storeMarkValid : accessValid ((capCheckGroupStartPrefix state 6).getReg .x30) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (capCheckGroupSteps state+fuel) state
      allowCoins =
      if (capCheckGroupResult state).2 then
        (do let result ← execute ((capExperimental 24).image .check) fuel
              (capCheckGroupResult state).1 allowCoins
            return result.charge (capCheckGroupSteps state) 0)
      else pure ⟨.failure,(capCheckGroupResult state).1,capCheckGroupSteps state,0⟩ := by
  let looked := capCheckGroupStartPrefix state 6
  let compared := capCheckGroupCompared state
  have branchState : capCheckGroupBranchState looked = compared := rfl
  have lookedPC : looked.pc = 4444 := by
    rw [cap_check_group_start_pc state 6 (by decide), pc]
    rfl
  have comparedScratch (i : Nat) (inside : i < 4) :
      accessValid (compared.getReg .x21+
        signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true := by
    change accessValid ((capCheckGroupBranchState looked).getReg .x21+
      signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true
    rw [cap_check_group_branch_register,
      cap_check_group_start_register state 6 (by decide) .x21 (by decide)]
    exact scratchValid i inside
  have comparedRoot (i : Nat) (inside : i < 4) :
      accessValid (compared.getReg .x23+
        signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true := by
    change accessValid ((capCheckGroupBranchState looked).getReg .x23+
      signExtend12 (BitVec.ofNat 12 (8*i))) 8 = true
    rw [cap_check_group_branch_register]
    exact rootValid i inside
  have comparedMark : accessValid (compared.getReg .x30) 8 = true := by
    change accessValid ((capCheckGroupBranchState looked).getReg .x30) 8 = true
    rw [cap_check_group_branch_register]
    exact storeMarkValid
  by_cases absent : looked.getReg .x6 = 0
  · have comparedPC : compared.pc = 4500 := by
      simp only [compared, capCheckGroupCompared, capCheckGroupBranchState,
        MachineState.setPC, show (capCheckGroupStartPrefix state 6).getReg .x6=0 from absent,
        ↓reduceIte]
    simp only [capCheckGroupSteps, capCheckGroupResult, show
      (capCheckGroupStartPrefix state 6).getReg .x6=0 from absent, ↓reduceIte]
    rw [show 16+fuel=6+(1+(9+fuel)) by omega,
      cap_check_group_start_execute state pc markValid,
      cap_check_group_branch_execute looked lookedPC, branchState,
      cap_check_group_store_execute compared comparedPC
        (fun i => comparedScratch i.val i.isLt)
        (fun i => comparedRoot i.val i.isLt) comparedMark]
    exact group_charge _ 9
  · have comparedPC : compared.pc = 4448 := by
      simp only [compared, capCheckGroupCompared, capCheckGroupBranchState,
        MachineState.setPC, show ¬(capCheckGroupStartPrefix state 6).getReg .x6=0 from absent,
        ↓reduceIte]
    cases passed : (capCheckDuplicateLoop compared 0 4).2
    · simp only [capCheckGroupSteps, capCheckGroupResult, show
        ¬(capCheckGroupStartPrefix state 6).getReg .x6=0 from absent, ↓reduceIte,
        show (capCheckDuplicateLoop (capCheckGroupCompared state) 0 4).2=false from passed,
        Bool.false_eq_true, ↓reduceIte]
      rw [show 7+capCheckDuplicateSteps compared 0 4+3+fuel =
          6+(1+(capCheckDuplicateSteps compared 0 4+3+fuel)) by omega,
        cap_check_group_start_execute state pc markValid,
        cap_check_group_branch_execute looked lookedPC, branchState,
        cap_check_duplicate_fail_execute compared comparedPC passed
          comparedScratch comparedRoot]
      simp [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      constructor
      · rfl
      · change 1+(3+(capCheckDuplicateSteps (capCheckGroupCompared state) 0 4+6)) =
          3+(capCheckDuplicateSteps (capCheckGroupCompared state) 0 4+7)
        omega
    · have steps : capCheckDuplicateSteps (capCheckGroupCompared state) 0 4 = 3*4 :=
        cap_check_duplicate_steps_passed compared 0 4 passed
      simp only [capCheckGroupSteps, capCheckGroupResult, show
        ¬(capCheckGroupStartPrefix state 6).getReg .x6=0 from absent, ↓reduceIte,
        show (capCheckDuplicateLoop (capCheckGroupCompared state) 0 4).2=true from passed,
        ↓reduceIte, steps]
      rw [show 7+3*4+1+fuel=6+(1+(13+fuel)) by omega,
        cap_check_group_start_execute state pc markValid,
        cap_check_group_branch_execute looked lookedPC, branchState,
        cap_check_duplicate_pass_execute compared comparedPC passed
          comparedScratch comparedRoot]
      exact group_charge _ 13

end CommitGolfCandidate
