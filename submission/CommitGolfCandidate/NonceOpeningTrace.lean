import CommitGolfCandidate.NonceOpeningFetch

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

inductive NonceOpeningTrace : Nat → MachineState → Execution → Prop where
  | halt (state : MachineState)
      (fetched : fetch nonceOldOpeningImage state=some (.base .ECALL))
      (selector : state.getReg .x5=1) (success : state.getReg .x10=0) :
      NonceOpeningTrace 1 state ⟨.success,state,1,0⟩
  | step {count : Nat} {state next : MachineState} {result : Execution}
      (instruction : Instruction)
      (fetched : fetch nonceOldOpeningImage state=some instruction)
      (stepped : ordinaryStep state instruction=some next)
      (tail : NonceOpeningTrace count next result) :
      NonceOpeningTrace (count+1) state (result.charge (instructionCycles instruction) 0)

theorem nonce_opening_trace_old {count : Nat} {state : MachineState} {result : Execution}
    (trace : NonceOpeningTrace count state result) (extra : Nat) (coins : Bool) :
    execute nonceOldOpeningImage (count+extra) state coins=pure result := by
  induction trace with
  | halt state fetched selector success =>
    rw [Nat.add_comm 1 extra]
    simp [execute, fetched, selector, success]
  | @step count state next result instruction fetched stepped tail ih =>
    rw [show count+1+extra=(count+extra)+1 by omega,
      execute_ordinary_step _ _ _ _ _ _ fetched stepped, ih]
    simp only [pure_bind]

theorem nonce_opening_trace_new {count : Nat} {state : MachineState} {result : Execution}
    (trace : NonceOpeningTrace count state result) (extra : Nat) (coins : Bool) :
    execute nonceCompactImage (count+extra) state coins=
      (do let final ← execute nonceCompactImage extra (result.state.setPC 4540) coins
          return final.charge result.cycles 0) := by
  induction trace with
  | halt state fetched selector success =>
    exact nonce_opening_halt_replacement state (nonce_opening_ecall_pc state fetched) extra coins
  | @step count state next result instruction fetched stepped tail ih =>
    have ordinary : instruction≠.base .ECALL := by
      intro equal
      subst instruction
      simp only [ordinaryStep] at stepped
      contradiction
    have newFetched:=nonce_opening_ordinary_fetch state instruction fetched ordinary
    rw [show count+1+extra=(count+extra)+1 by omega,
      execute_ordinary_step _ _ _ _ _ _ newFetched stepped, ih]
    simp [Execution.charge, Nat.add_assoc]

theorem nonce_opening_trace_queries {count : Nat} {state : MachineState} {result : Execution}
    (trace : NonceOpeningTrace count state result) : result.oracleCalls=0 := by
  induction trace with
  | halt => rfl
  | step instruction fetched stepped tail ih => simpa only [Execution.charge, Nat.zero_add] using ih

theorem nonce_opening_trace_positive {count : Nat} {state : MachineState} {result : Execution}
    (trace : NonceOpeningTrace count state result) : 0<count := by
  cases trace <;> omega

end CommitGolfCandidate
