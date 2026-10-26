import CommitGolf.Honest

/-! # Binding game

Position binding [CY24, Lemma 18.4.1]. The declared instances are independent. Finite-domain
instances are sampled eagerly; infinite-domain random oracles use shared lazy caches. The
adversary outputs a commitment and two openings of it. It wins if `check` accepts both and they
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

/-- Sample a finite-domain family and run the adversary against it. Returns the same realization,
the claim, and the number of calls the adversary made. The two checks use that realization too. -/
def bindingGame {family : OracleFamily} (adversary : Adversary family)
    (finite : family.Finite := by decide) :
    ProbComp (family.Realization × Claim × Nat) := do
  let π ← family.sample finite
  let (claim, calls) ← family.run π adversary
  return (π, claim, calls)

/-- Infinite-domain binding experiment. The adversary and both checks share one cache per
instance. Only the adversary's calls are returned; verifier queries can extend the caches. -/
def sharedBindingGame (adversary : Adversary scheme.oracles) :
    ProbComp (Claim × Nat × Bool × Bool) := do
  let initial ← scheme.oracles.initialState
  let experiment : StateT scheme.oracles.State ProbComp (Claim × Nat × Bool × Bool) := do
    let (claim, calls) ← scheme.oracles.runShared adversary
    let accepted₀ ← scheme.oracles.checkShared
      (scheme.check claim.root claim.positions₀ claim.values₀ claim.proof₀)
    let accepted₁ ← scheme.oracles.checkShared
      (scheme.check claim.root claim.positions₁ claim.values₁ claim.proof₁)
    return (claim, calls, accepted₀, accepted₁)
  return (← experiment.run initial).1

/-- The finite-domain game retains its eager semantics. For infinite domains we sample only
queried answers, including fresh verifier queries, consistently across the whole game. -/
noncomputable def bindingProbability (adversary : Adversary scheme.oracles) (q : Nat) : ENNReal :=
  if h : scheme.oracles.Finite then
    Pr[fun (π, claim, calls) => scheme.Breaks π claim ∧ calls ≤ q | bindingGame adversary h]
  else
    Pr[fun (claim, calls, a₀, a₁) => claim.Conflicting ∧ calls ≤ q ∧ a₀ = true ∧ a₁ = true |
      scheme.sharedBindingGame adversary]

end Scheme

end CommitGolf
