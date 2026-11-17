import CommitGolfCandidate.CapCountedLoop

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem cap_counted_run_execute_costed (image : Image) (steps cycles : Nat)
    (step : MachineState → MachineState) (ready : Nat → MachineState → Prop)
    (transport : ∀ remaining state, ready (remaining+1) state → ready remaining (step state))
    (checked : ∀ remaining state, ready (remaining+1) state →
      ∀ fuel allowCoins, execute image (steps+fuel) state allowCoins =
        (do let result ← execute image fuel (step state) allowCoins
            return result.charge cycles 0))
    (remaining : Nat) (state : MachineState) (valid : ready remaining state)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (steps*remaining+fuel) state allowCoins =
      (do let result ← execute image fuel (capCountedRun step remaining state) allowCoins
          return result.charge (cycles*remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [capCountedRun, Execution.charge]
  | succ remaining ih =>
    rw [show steps*(remaining+1)+fuel=steps+(steps*remaining+fuel) by
        simp only [Nat.mul_add, Nat.mul_one]
        omega,
      checked remaining state valid, ih (step state) (transport remaining state valid)]
    simp only [bind_assoc, pure_bind, capCountedRun]
    simp [Execution.charge, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end CommitGolfCandidate
