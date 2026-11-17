import CommitGolfCandidate.CapDfsStable

/-! One actual DFS macro, including its exact instruction, cycle and query
charges. Boundary admission is required only at an unknown visit; the checker
short-input alternative is handled by the separate guard/rejection bridge.
No fixed oracle is assumed by this operational transition. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

structure CapDfsBoundaryReady (checking : Bool) (state : MachineState)
    (rootBase node : Nat) where
  cursor : Nat
  pointer : state.getReg .x25 = BitVec.ofNat 64 cursor
  aligned : cursor % 8 = 0
  bound : cursor + 32 ≤ MEMORY_BYTES
  rootBound : rootBase + 32 * node + 32 ≤ MEMORY_BYTES
  rootAligned : rootBase % 8 = 0
  limit : Nat
  proofEnd : checking = true → state.getReg .x22 = BitVec.ofNat 64 limit
  limitBound : checking = true → limit ≤ MEMORY_BYTES
  enough : checking = true → cursor + 32 ≤ limit
  highOutput : checking = false → 32768 ≤ cursor

def capDfsStep (checking : Bool) (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState) : OracleComp World MachineState :=
  match control with
  | .visit node =>
      if marked node then pure (capMarkedVisitState checking state node)
      else if checking then pure (capUnknownCheckState state)
      else pure (capUnknownOpenState state)
  | .advance node =>
      if node = 1 then pure (capAdvanceRootState checking state)
      else if node % 2 = 0 then pure (capAdvanceSiblingState checking state)
      else if checking then do
        let answer ← capCheckCompression (capCheckAscentQuery state node)
        return capCheckAscentAnswer state answer
      else pure (capAdvanceOpenAscentState state)
  | .done => pure state

def capDfsStepInstructions (checking : Bool) (marked : Nat → Bool) : CapDfsControl → Nat
  | .visit node =>
      if marked node then 4 + (if node < 256 then 3 else 1)
      else if checking then 17 else 15
  | .advance node =>
      if node = 1 then 1 else if node % 2 = 0 then 5 else if checking then 10 else 5
  | .done => 0

def capDfsStepCycles (checking : Bool) (marked : Nat → Bool) : CapDfsControl → Nat
  | .advance node =>
      if node = 1 then 1 else if node % 2 = 0 then 5 else if checking then 17 else 5
  | control => capDfsStepInstructions checking marked control

def capDfsStepQueries (checking : Bool) : CapDfsControl → Nat
  | .advance node =>
      if node = 1 then 0 else if node % 2 = 0 then 0 else if checking then 1 else 0
  | _ => 0

private theorem charge_zero (result : Execution) : result.charge 0 0 = result := by
  simp only [Execution.charge, Nat.zero_add]

theorem cap_dfs_step_execute (checking : Bool) (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState) (rootBase : Nat)
    (physical : CapDfsStateControl checking state control)
    (valid : CapDfsControlValid control) (stable : CapDfsStable checking state rootBase)
    (ready : CapMarksReady state 256 0 marked)
    (checkBase : checking = true → rootBase = 12288)
    (boundary : ∀ node, control = .visit node → marked node = false →
      CapDfsBoundaryReady checking state rootBase node)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking)
        (capDfsStepInstructions checking marked control + fuel) state allowCoins =
      (do let next ← capDfsStep checking marked control state
          let result ← execute (capWalkImage checking) fuel next allowCoins
          return result.charge (capDfsStepCycles checking marked control)
            (capDfsStepQueries checking control)) := by
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simpa only [capDfsStepInstructions, capDfsStepCycles, capDfsStepQueries,
          capDfsStep, present, ↓reduceIte, pure_bind] using
          cap_marked_visit_execute checking state node physical.1 stable.marks physical.2
            stable.leaves valid.1 valid.2 marked ready present fuel allowCoins
      · have absent : marked node = false := Bool.eq_false_iff.mpr present
        have admitted := boundary node rfl absent
        cases checking
        · simpa only [capDfsStepInstructions, capDfsStepCycles, capDfsStepQueries,
            capDfsStep, absent, Bool.false_eq_true, ↓reduceIte, pure_bind] using
            cap_unknown_open_execute state node rootBase admitted.cursor physical.1
              stable.marks physical.2 valid.1 valid.2 marked ready absent stable.roots
              admitted.rootBound admitted.rootAligned admitted.pointer admitted.bound
              admitted.aligned fuel allowCoins
        · have base : rootBase = 12288 := checkBase rfl
          have roots : state.getReg .x18 = 12288 := by
            change state.getReg .x18 = BitVec.ofNat 64 12288
            simpa only [base, capBoundaryRootRegister, ↓reduceIte] using stable.roots
          simpa only [capDfsStepInstructions, capDfsStepCycles, capDfsStepQueries,
            capDfsStep, absent, Bool.false_eq_true, ↓reduceIte, pure_bind] using
            cap_unknown_check_execute state node admitted.cursor admitted.limit physical.1
              stable.marks physical.2 valid.1 valid.2 marked ready absent roots
              admitted.pointer (admitted.proofEnd rfl) (admitted.limitBound rfl)
              (admitted.enough rfl) admitted.aligned fuel allowCoins
  | advance node =>
      by_cases root : node = 1
      · simpa only [capDfsStepInstructions, capDfsStepCycles, capDfsStepQueries,
          capDfsStep, root, ↓reduceIte, pure_bind] using
          cap_advance_root_execute checking state physical.1 fuel allowCoins
      · by_cases even : node % 2 = 0
        · simpa only [capDfsStepInstructions, capDfsStepCycles, capDfsStepQueries,
            capDfsStep, if_neg root, if_pos even, pure_bind] using
            cap_advance_sibling_execute checking state node physical.1 physical.2
              stable.root valid.2 root even fuel allowCoins
        · cases checking
          · simpa only [capDfsStepInstructions, capDfsStepCycles, capDfsStepQueries,
              capDfsStep, if_neg root, if_neg even, Bool.false_eq_true, ↓reduceIte,
              pure_bind] using
              cap_advance_open_ascent_execute state node physical.1 physical.2
                stable.root valid.2 root even fuel allowCoins
          · have base : rootBase = 12288 := checkBase rfl
            have roots : state.getReg .x18 = 12288 := by
              change state.getReg .x18 = BitVec.ofNat 64 12288
              simpa only [base, capBoundaryRootRegister, ↓reduceIte] using stable.roots
            simpa only [capDfsStepInstructions, capDfsStepCycles, capDfsStepQueries,
              capDfsStep, if_neg root, if_neg even, ↓reduceIte, bind_assoc, pure_bind] using
              cap_check_ascent_execute state node physical.1 physical.2 stable.root valid.2
                root even roots (stable.selectors rfl) fuel allowCoins
  | done =>
      simp only [capDfsStepInstructions, capDfsStepCycles, capDfsStepQueries,
        capDfsStep, pure_bind, Nat.zero_add, charge_zero]
      exact (bind_pure _).symm

end CommitGolfCandidate
