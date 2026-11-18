import CommitGolfCandidate.Execution

/-! Compose an actual fetched trace with instruction-dependent cycle charges.
The instruction reserve still counts transitions, separately from their costs. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def linearTraceCost : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | count+1, costs => costs 0 + linearTraceCost count (fun i => costs (i+1))

theorem execute_costed_steps (image : Image) (count fuel : Nat)
    (states : Nat → MachineState) (costs : Nat → Nat) (allowCoins : Bool)
    (trace : ∀ i < count, ∃ instruction,
      fetch image (states i) = some instruction ∧
      ordinaryStep (states i) instruction = some (states (i+1)) ∧
      instructionCycles instruction = costs i) :
    execute image (count+fuel) (states 0) allowCoins =
      (do let result ← execute image fuel (states count) allowCoins
          return result.charge (linearTraceCost count costs) 0) := by
  induction count generalizing states costs with
  | zero => simp [linearTraceCost, Execution.charge]
  | succ count ih =>
    obtain ⟨instruction, fetched, stepped, cost⟩ := trace 0 (by omega)
    rw [Nat.succ_add, execute_ordinary_step image instruction _ _ _ _ fetched stepped, cost]
    have tail := ih (fun i => states (i+1)) (fun i => costs (i+1)) (by
      intro i inside
      exact trace (i+1) (by omega))
    simp only [tail, bind_assoc, pure_bind]
    simp [linearTraceCost, Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end CommitGolfCandidate
