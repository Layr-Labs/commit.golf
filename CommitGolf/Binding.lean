import CommitGolf.Honest

/-! # Binding game

Position binding, as in [CY24, Lemma 18.4.1]: no adversary making few permutation calls can open
one commitment to two different values at the same position.

**The game.**
1. Draw a uniform permutation `π`.
2. The adversary `A`, with access to `π` and `π⁻¹`, outputs a commitment and two openings of it:
   `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)`.
3. `A` wins if both openings are accepted, `check(rt, I₀, a₀, pf₀) = 1` and
   `check(rt, I₁, a₁, pf₁) = 1`, and they *conflict*: some position `i ∈ I₀ ∩ I₁` has
   `a₀[i] ≠ a₁[i]`.

The commitment need not come from `commit`: the adversary chooses it freely.

**What is counted.** Only the adversary's own calls to `π` and `π⁻¹`, as in [CY24]. The calls
`check` makes on the adversary's output are not counted, so a slow `check` cannot make the binding
bound easier to meet. `Statements.Binding` bounds the winning probability in terms of this count. -/

namespace CommitGolf
open OracleComp OracleSpec

namespace Scheme
variable (scheme : Scheme)

/-- The adversary's output: one commitment and two openings of it,
`(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)`. -/
structure Claim where
  root : Commitment
  positions₀ : Positions
  values₀ : Values positions₀
  proof₀ : Proof
  positions₁ : Positions
  values₁ : Values positions₁
  proof₁ : Proof

/-- A classical adversary: a probabilistic computation that may query `π` and `π⁻¹` and outputs
a claim. Its local computation is unrestricted (any Lean function, computable or not); only the
answers of its oracles carry information about `π`.

Its queries are: coins as `.inl _`, `π` as `.inr (.inl _)`, and `π⁻¹` as `.inr (.inr _)`. Every
`OracleComp` makes finitely many queries on each run; an adaptive strategy that might run for ever
is covered by its truncations. -/
abbrev Adversary := OracleComp World Claim

/-- The two openings disagree at a position that both of them open. -/
def Claim.Conflicting (claim : Claim) : Prop :=
  ∃ (i : Index) (h₀ : i ∈ claim.positions₀) (h₁ : i ∈ claim.positions₁),
    claim.values₀ ⟨i, h₀⟩ ≠ claim.values₁ ⟨i, h₁⟩

/-- The claim wins against `π`: the openings conflict, and `check` accepts both under `π`. -/
def Breaks (π : Perm) (claim : Claim) : Prop :=
  claim.Conflicting ∧
    (π.eval (scheme.check claim.root claim.positions₀ claim.values₀ claim.proof₀)).1 = true ∧
    (π.eval (scheme.check claim.root claim.positions₁ claim.values₁ claim.proof₁)).1 = true

/-- The binding game: draw a uniform permutation and run the adversary against it. Returns the
permutation, the adversary's claim, and the number of permutation calls the adversary made.
`Statements.Binding` then asks whether `Breaks π claim` holds. -/
def bindingGame (adversary : Adversary) : ProbComp (Perm × Claim × Nat) := do
  let π ← $ᵗ Perm
  let (claim, calls) ← π.run adversary
  return (π, claim, calls)

end Scheme

end CommitGolf
