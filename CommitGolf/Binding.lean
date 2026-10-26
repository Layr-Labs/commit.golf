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

/-- Check both openings against the shared oracle state. Fresh random-oracle queries extend
that state, so the second check reuses answers from the adversary and the first check. -/
def checkClaim (claim : Claim) : StateT scheme.oracles.State ProbComp (Bool × Bool) := do
  let accepted₀ ← scheme.oracles.checkShared
    (scheme.check claim.root claim.positions₀ claim.values₀ claim.proof₀)
  let accepted₁ ← scheme.oracles.checkShared
    (scheme.check claim.root claim.positions₁ claim.values₁ claim.proof₁)
  return (accepted₀, accepted₁)

/-- Binding experiment for every oracle family. The adversary and both checks share the oracle
state. Only the adversary's calls are returned; verifier queries can extend random-oracle caches. -/
def bindingGame (adversary : Adversary scheme.oracles) :
    ProbComp (Claim × Nat × Bool × Bool) := do
  let initial ← scheme.oracles.initialState
  let experiment : StateT scheme.oracles.State ProbComp (Claim × Nat × Bool × Bool) := do
    let (claim, calls) ← scheme.oracles.runShared adversary
    let (accepted₀, accepted₁) ← scheme.checkClaim claim
    return (claim, calls, accepted₀, accepted₁)
  return (← experiment.run initial).1

end Scheme

end CommitGolf
