import CommitGolfCandidate.NonceOpeningFetch

/-! Ordinary traces of the cap-level opener. A deterministic run (`execute .. = pure result`)
without coins that succeeds is a trace of ordinary steps ending at a HALT; replayed in the delivered
image, the trace reaches the compaction with the same charges. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

inductive NonceOpeningTrace : Nat → MachineState → Execution → Prop where
  | halt (state : MachineState)
      (fetched : fetch nonceOldOpeningImage state = some (.base .ECALL))
      (selector : state.getReg .x5 = 1) (success : state.getReg .x10 = 0) :
      NonceOpeningTrace 1 state ⟨.success, state, 1, 0⟩
  | step {count : Nat} {state next : MachineState} {result : Execution}
      (instruction : Instruction)
      (fetched : fetch nonceOldOpeningImage state = some instruction)
      (ordinary : instruction ≠ .base .ECALL)
      (stepped : ordinaryStep state instruction = some next)
      (tail : NonceOpeningTrace count next result) :
      NonceOpeningTrace (count + 1) state (result.charge (instructionCycles instruction) 0)

theorem nonce_opening_trace_state {count : Nat} {state : MachineState} {result : Execution}
    (trace : NonceOpeningTrace count state result) :
    ∃ final, result.state = final ∧ fetch nonceOldOpeningImage final = some (.base .ECALL) := by
  induction trace with
  | halt state fetched => exact ⟨state, rfl, fetched⟩
  | step instruction fetched ordinary stepped tail ih =>
    obtain ⟨final, same, fetchedFinal⟩ := ih
    exact ⟨final, same, fetchedFinal⟩

/-- A coin-free deterministic successful run is an ordinary trace. -/
theorem nonce_pure_trace (fuel : Nat) (state : MachineState) (result : Execution)
    (run : execute nonceOldOpeningImage fuel state false = pure result)
    (success : result.exit = .success) :
    ∃ count, count ≤ fuel ∧ NonceOpeningTrace count state result := by
  induction fuel generalizing state result with
  | zero =>
    simp only [execute] at run
    rw [OracleComp.pure_inj] at run
    subst result
    cases success
  | succ fuel ih =>
    cases fetched : fetch nonceOldOpeningImage state with
    | none =>
      simp only [execute, fetched] at run
      rw [OracleComp.pure_inj] at run
      subst result
      cases success
    | some instruction =>
      by_cases syscall : instruction = .base .ECALL
      · subst instruction
        simp only [execute, fetched] at run
        by_cases oracleSelector : state.getReg .x5 = 0
        · rw [if_pos oracleSelector] at run
          cases input : oracleInput state with
          | none =>
            rw [input] at run
            simp only at run
            rw [OracleComp.pure_inj] at run
            subst result
            cases success
          | some query =>
            rw [input] at run
            simp only at run
            obtain ⟨answer, queried, _⟩ := (OracleComp.bind_eq_pure_iff _ _ _).mp run
            exact absurd queried (OracleComp.query_ne_pure _ _)
        · rw [if_neg oracleSelector] at run
          by_cases haltSelector : state.getReg .x5 = 1
          · rw [if_pos haltSelector] at run
            rw [OracleComp.pure_inj] at run
            subst result
            by_cases exitZero : state.getReg .x10 = 0
            · simp only [exitZero, ↓reduceIte]
              exact ⟨1, by omega, NonceOpeningTrace.halt state fetched haltSelector exitZero⟩
            · simp only [exitZero, ↓reduceIte] at success
              cases success
          · rw [if_neg haltSelector] at run
            simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at run
            rw [OracleComp.pure_inj] at run
            subst result
            cases success
      · cases stepped : ordinaryStep state instruction with
        | none =>
          have failure : execute nonceOldOpeningImage (fuel + 1) state false =
              pure ⟨.failure, state, 1, 0⟩ := by
            cases instruction with
            | base instruction => cases instruction <;> simp_all [execute, ordinaryStep]
            | word op rd rs1 rs2 => simp_all [execute, ordinaryStep]
            | sraiw rd rs shift => simp_all [execute, ordinaryStep]
          rw [failure, OracleComp.pure_inj] at run
          subst result
          cases success
        | some next =>
          rw [execute_ordinary_step nonceOldOpeningImage instruction state next fuel false fetched stepped]
            at run
          obtain ⟨tail, tailRun, charged⟩ := (OracleComp.bind_eq_pure_iff _ _ _).mp run
          rw [OracleComp.pure_inj] at charged
          subst result
          have tailSuccess : tail.exit = .success := by simpa [Execution.charge] using success
          obtain ⟨count, bounded, trace⟩ := ih next tail tailRun tailSuccess
          exact ⟨count + 1, by omega, NonceOpeningTrace.step instruction fetched syscall stepped trace⟩

theorem nonce_charge_state (result : Execution) (cycles calls : Nat) :
    (result.charge cycles calls).state = result.state := rfl

/-- Replay of a trace in the delivered image, the final HALT (at word 110) becoming the jump. -/
theorem nonce_opening_trace_new {count : Nat} {state : MachineState} {result : Execution}
    (trace : NonceOpeningTrace count state result) (haltPc : result.state.pc = 4536)
    (extra : Nat) (coins : Bool) :
    execute s6OpeningImage (count + extra) state coins =
      (do let final ← execute s6OpeningImage extra (result.state.setPC 4864) coins
          return final.charge result.cycles 0) := by
  induction trace with
  | halt state fetched selector success =>
    exact nonce_opening_halt_replacement state haltPc extra coins
  | @step count state next result instruction fetched ordinary stepped tail ih =>
    have newFetched := nonce_opening_ordinary_fetch state instruction fetched ordinary
    rw [show count + 1 + extra = (count + extra) + 1 by omega,
      execute_ordinary_step _ _ _ _ _ _ newFetched stepped, ih haltPc]
    simp [Execution.charge, Nat.add_assoc]

theorem nonce_opening_trace_calls {count : Nat} {state : MachineState} {result : Execution}
    (trace : NonceOpeningTrace count state result) : result.oracleCalls = 0 := by
  induction trace with
  | halt => rfl
  | step instruction fetched ordinary stepped tail ih =>
    simpa only [Execution.charge, Nat.zero_add] using ih

end CommitGolfCandidate
