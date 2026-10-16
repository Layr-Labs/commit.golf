import CommitGolf.Honest

/-! # Binding game

Position binding [CY24, Lemma 18.4.1]. Draw a uniform `π`; the adversary, with access to `π` and
`π⁻¹`, outputs a commitment and two openings of it. It wins if `check` accepts both and they
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
abbrev Adversary := OracleComp World Claim

/-- Some position in both `I₀` and `I₁` has different values in `a₀` and `a₁`. -/
def Claim.Conflicting (claim : Claim) : Prop :=
  ∃ (i : Index) (h₀ : i ∈ claim.positions₀) (h₁ : i ∈ claim.positions₁),
    claim.values₀ ⟨i, h₀⟩ ≠ claim.values₁ ⟨i, h₁⟩

/-- The claim wins against `π`: the openings conflict, and `check` accepts both. -/
def Breaks (π : Perm) (claim : Claim) : Prop :=
  claim.Conflicting ∧
    (π.eval (scheme.check claim.root claim.positions₀ claim.values₀ claim.proof₀)).1 = true ∧
    (π.eval (scheme.check claim.root claim.positions₁ claim.values₁ claim.proof₁)).1 = true

/-- Draw a uniform `π` and run the adversary against it. Returns `π`, the claim, and the number of
calls the adversary made. -/
def bindingGame (adversary : Adversary) : ProbComp (Perm × Claim × Nat) := do
  let π ← $ᵗ Perm
  let (claim, calls) ← π.run adversary
  return (π, claim, calls)

end Scheme

end CommitGolf
