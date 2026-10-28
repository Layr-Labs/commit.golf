import CommitGolf.Binding
import CommitGolf.Oracle.Finite

/-! # Compatibility with the original finite-domain binding experiment

The security definition uses one shared-state game for all tracks. These lemmas show that
finite-domain families have exactly the original winning probability, allowing existing
proofs to use the eager experiment as a proof technique. -/
namespace CommitGolf.Scheme
open OracleComp OracleSpec

/-- The original eager experiment, used only in finite-domain compatibility proofs. -/
def finiteBindingGame {family : OracleFamily} (adversary : Adversary family)
    (finite : family.HasFiniteDomain := by decide) :
    ProbComp (family.Realization × Claim × Nat) := do
  let H ← family.sample finite
  let (claim, calls) ← family.run H adversary
  return (H, claim, calls)

variable (scheme : Scheme)

/-- Shared execution of finite-domain oracles preserves the sampled realization. -/
theorem bindingGame_eq_finite {family : OracleFamily} (h : family.HasFiniteDomain)
    (adversary : Adversary family) :
    bindingGame adversary = (fun (H, claim, calls) =>
      (family.stateOf h H, claim, calls)) <$> finiteBindingGame adversary h := by
  simp [bindingGame, finiteBindingGame, OracleFamily.initialState_eq_sample _ h,
    OracleFamily.runShared_stateOf, map_eq_bind_pure_comp]

/-- Exact preservation of the old security statement for every finite-domain family. -/
theorem bindingProbability_eq_finite (h : scheme.oracles.HasFiniteDomain)
    (adversary : Adversary scheme.oracles) (q : Nat) :
    Pr[fun (claim, calls, a₀, a₁) => claim.Conflicting ∧ calls ≤ q ∧ a₀ = true ∧ a₁ = true | do
        let (π, claim, calls) ← bindingGame adversary
        let ((a₀, a₁), _) ← (scheme.checkClaim claim).run π
        return (claim, calls, a₀, a₁)] =
      Pr[fun (H, claim, calls) => scheme.Breaks H claim ∧ calls ≤ q |
        finiteBindingGame adversary h] := by
  rw [bindingGame_eq_finite h]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  simp [checkClaim, StateT.run_bind, OracleFamily.checkShared_stateOf]
  congr 1
  funext ⟨H, claim, calls⟩
  simp [Breaks, and_assoc, and_left_comm, and_comm]

end CommitGolf.Scheme
