import CommitGolfCandidate.Stage3cRngInvariant

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def applyPairs : Nat → MachineState → List Draw40 → MachineState
  | _, s, [] => s
  | p, s, w::ws => applyPairs (p+1) (nextPair p s w) ws

def samplingSteps (p count : Nat) := 2*count + 3*((p+count)/2048-p/2048)-(if p<pairCount ∧ p+count=pairCount then 1 else 0)
def samplingCycles (p count : Nat) := 7*count + 3*((p+count)/2048-p/2048)-(if p<pairCount ∧ p+count=pairCount then 1 else 0)

/-- Execute the tiled loop with one independent 320-bit draw at each pair.
Fuel and cycle charges include both control instructions at each tile boundary. -/
theorem execute_pairs (ordinals : List Nat) (p : Nat) (s : MachineState)
    (a : AtPair s p) (enough : p + ordinals.length ≤ pairCount) (fuel : Nat) :
    execute commitImage (fuel+samplingSteps p ordinals.length) s true =
      (do let words ← ordinals.mapM fun _ => draw40
          let r ← execute commitImage fuel (applyPairs p s words) true
          return r.charge (samplingCycles p ordinals.length) 0) := by
  induction ordinals generalizing p s with
  | nil => simp [samplingSteps, samplingCycles, applyPairs, Execution.charge]
  | cons _ os ih =>
    have hi : p < pairCount := by simp only [List.length_cons] at enough; omega
    have enough' : p+1+os.length ≤ pairCount := by simp only [List.length_cons] at enough; omega
    have steps : fuel + samplingSteps p (os.length+1) =
        fuel + samplingSteps (p+1) os.length + pairSteps p := by
      unfold samplingSteps pairSteps extra pairCount at *
      split_ifs <;> omega
    have price : samplingCycles p (os.length+1) = pairCycles p + samplingCycles (p+1) os.length := by
      unfold samplingCycles pairCycles extra pairCount at *
      split_ifs <;> omega
    simp only [List.mapM_cons, List.length_cons, steps, execute_one_pair a hi,
      bind_assoc, pure_bind, applyPairs]
    apply bind_congr
    intro w
    rw [ih (p+1) (nextPair p s w) (next_pair_invariant a hi w) enough']
    simp only [bind_assoc, pure_bind, price, Execution.charge, Nat.add_assoc, Nat.zero_add]

theorem apply_pairs_invariant (ws : List Draw40) (p : Nat) (s : MachineState)
    (a : AtPair s p) (enough : p+ws.length ≤ pairCount) :
    AtPair (applyPairs p s ws) (p+ws.length) := by
  induction ws generalizing p s with
  | nil => simpa [applyPairs] using a
  | cons w ws ih =>
    simp only [List.length_cons] at enough ⊢
    simpa only [applyPairs, show p+1+ws.length = p+(ws.length+1) by omega] using
      ih (p+1) _ (next_pair_invariant a (by omega) w) (by omega)

end CommitGolfCandidate.Chained.BinaryMachine
