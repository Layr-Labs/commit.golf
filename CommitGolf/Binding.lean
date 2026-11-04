import CommitGolf.Honest

/-! # Binding game

Position binding [CY24, Lemma 18.4.1]. Sample both fixed primitives independently; the adversary outputs a commitment and two openings. It wins if `check` accepts both and they
disagree at a position both open. Only the adversary's own calls are counted, as in [CY24].

CY24's SNARG soundness arguments use [extractability, Lemma 18.5.1][cy24-extraction]. Its
deterministic extractor sees the commitment and the query/answer trace available when that
commitment is output, then returns a message and trapdoor before the opening continuation.
In that bounded-query two-phase game, failure includes inconsistent accepted values or a
proof differing from the canonical proof regenerated from the extracted trapdoor. The lemma
also bounds extractor runtime. This causal extraction contract is not required here.
[Remark 18.5.6][cy24-binding] derives position binding with at most twice the extraction
error, for the same adversary query budget. This certificate supplies position binding alone,
not a drop-in premise for those SNARG theorems.

[cy24-extraction]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.pdf#page=214
[cy24-binding]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.pdf#page=218
-/

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

/-- The claim wins against the fixed oracle pair `π`: the openings conflict, and `check` accepts both. -/
def Breaks (π : Oracle) (claim : Claim) : Prop :=
  claim.Conflicting ∧
    (π.eval (scheme.check claim.root claim.positions₀ claim.values₀ claim.proof₀)).1 = true ∧
    (π.eval (scheme.check claim.root claim.positions₁ claim.values₁ claim.proof₁)).1 = true

/-- Sample the oracle functions once and run the adversary against them. Both checks
use this same realization. Only the adversary's calls contribute to the budget. -/
def bindingGame (adversary : Adversary) : ProbComp (Oracle × Claim × Nat) := do
  let oracle ← Oracle.sample
  let (claim, calls) ← oracle.run adversary
  return (oracle, claim, calls)

end Scheme

end CommitGolf
