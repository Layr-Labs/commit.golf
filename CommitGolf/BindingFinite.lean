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

/-- The claim wins against the fixed family `π`: the openings conflict, and `check` accepts both. -/
def Breaks (π : scheme.oracles.Realization) (claim : Claim) : Prop :=
  claim.Conflicting ∧
    (scheme.oracles.eval π (scheme.check claim.root claim.positions₀ claim.values₀ claim.proof₀)).1 = true ∧
    (scheme.oracles.eval π (scheme.check claim.root claim.positions₁ claim.values₁ claim.proof₁)).1 = true

/-- Shared execution of finite-domain oracles gives the same answers as the original game. -/
theorem bindingGame_eq_finite (h : scheme.oracles.HasFiniteDomain)
    (adversary : Adversary scheme.oracles) :
    scheme.bindingGame adversary = (fun (H, claim, calls) =>
      (claim, calls,
        (scheme.oracles.eval H (scheme.check claim.root claim.positions₀ claim.values₀ claim.proof₀)).1,
        (scheme.oracles.eval H (scheme.check claim.root claim.positions₁ claim.values₁ claim.proof₁)).1)) <$>
      finiteBindingGame adversary h := by
  simp [bindingGame, finiteBindingGame, OracleFamily.initialState_eq_sample _ h,
    StateT.run_bind, OracleFamily.runShared_stateOf, OracleFamily.checkShared_stateOf,
    map_eq_bind_pure_comp]

/-- Exact preservation of the old security statement for every finite-domain family. -/
theorem bindingProbability_eq_finite (h : scheme.oracles.HasFiniteDomain)
    (adversary : Adversary scheme.oracles) (q : Nat) :
    scheme.bindingProbability adversary q =
      Pr[fun (H, claim, calls) => scheme.Breaks H claim ∧ calls ≤ q |
        finiteBindingGame adversary h] := by
  rw [bindingProbability, scheme.bindingGame_eq_finite h, probEvent_map]
  congr 1
  funext ⟨H, claim, calls⟩
  simp [Breaks, and_assoc, and_left_comm, and_comm]

end CommitGolf.Scheme
