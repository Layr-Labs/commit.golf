import CommitGolf.Honest

/-! # Binding game

Position binding [CY24, Lemma 18.4.1]. Sample the declared oracle instances independently; the adversary outputs a commitment and two openings of it. It wins if `check` accepts both and they
disagree at a position both open. Only the adversary's own calls are counted, as in [CY24]. -/

namespace CommitGolf
open OracleComp OracleSpec

namespace Scheme
variable (scheme : Scheme)

/-- The adversary's output `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)`. -/
structure Claim where
  root : Commitment
  positions₀ : Positions
  values₀ : Values positions₀
  proof₀ : Proof
  positions₁ : Positions
  values₁ : Values positions₁
  proof₁ : Proof

/-- A classical adversary with unbounded computation and private coins. -/
abbrev Adversary (family : OracleFamily := OracleFamily.baseline) :=
  OracleComp family.world Claim

/-- Some position in both `I₀` and `I₁` has different values in `a₀` and `a₁`. -/
def Claim.Conflicting (claim : Claim) : Prop :=
  ∃ (i : Index) (h₀ : i ∈ claim.positions₀) (h₁ : i ∈ claim.positions₁),
    claim.values₀ ⟨i, h₀⟩ ≠ claim.values₁ ⟨i, h₁⟩

/-- The claim wins against the fixed family `π`: the openings conflict, and `check` accepts both. -/
def Breaks (π : scheme.oracles.Realization) (claim : Claim) : Prop :=
  claim.Conflicting ∧
    (scheme.oracles.eval π (scheme.check claim.root claim.positions₀ claim.values₀ claim.proof₀)).1 = true ∧
    (scheme.oracles.eval π (scheme.check claim.root claim.positions₁ claim.values₁ claim.proof₁)).1 = true

/-- Sample the declared family and run the adversary against it. Returns the same realization,
the claim, and the number of calls the adversary made. The two checks use that realization too. -/
def bindingGame {family : OracleFamily} (adversary : Adversary family) :
    ProbComp (family.Realization × Claim × Nat) := do
  let π ← family.sample
  let (claim, calls) ← family.run π adversary
  return (π, claim, calls)

end Scheme

end CommitGolf
