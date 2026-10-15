import CommitGolf.Binding

/-! # Statements

The five properties a submission proves, in the order `RULES.md` lists them, and the `Certificate`
bundling them. The certificate for a scheme and two claimed scores is the competition claim.

Probabilities and expectations are valued in `ENNReal`, the nonnegative reals extended with `∞`.
`expectedValue c g` is the expectation of `g r` when `r` is the result of the computation `c`. -/

namespace CommitGolf
open OracleComp OracleComp.EvalDist

namespace Scheme
variable (scheme : Scheme)

/-- **1. Completeness** ([CY24, Lemma 18.2.1]), *perfect*: for every permutation, message, and set
of positions, and for all coins of `commit` and `opening`, `check` accepts the honest opening.

Quantifying over every `π`, `m`, and `I` covers every adversary that picks `(m, I)` in [CY24],
even one that sees `π` first. -/
def Completeness : Prop :=
  ∀ (π : Perm) (message : Message) (positions : Positions),
    Pr[fun result => result.accepted = true | scheme.honest π message positions] = 1

/-- **2. Honest budgets.** For every permutation, message, set of positions `I`, and for all coins,
`commit` makes at most `COMMIT_BUDGET` permutation calls and `opening` at most `OPEN_BUDGET |I|`. -/
def HonestBudgets : Prop :=
  ∀ (π : Perm) (message : Message) (positions : Positions),
    Pr[fun result => result.commitCalls ≤ COMMIT_BUDGET ∧
        result.openCalls ≤ OPEN_BUDGET positions.card |
      scheme.honest π message positions] = 1

/-- **3. Proof size**, the first score: for every message, the expected length in bytes of the
opening proof is at most `proofBytes`. The expectation is over the scored run: a uniform
permutation, a uniform set of `BATCH` distinct positions, and the scheme's coins. -/
def ProofSize (proofBytes : Nat) : Prop :=
  ∀ message : Message,
    expectedValue (scheme.scoredRun message) (fun result => (result.proofBytes : ENNReal)) ≤
      proofBytes

/-- **4. Verification cost**, the second score: for every message, the expected number of
permutation calls `check` makes on the honest opening is at most `checkCalls`, over the same
scored run as `ProofSize`. -/
def VerificationCost (checkCalls : Nat) : Prop :=
  ∀ message : Message,
    expectedValue (scheme.scoredRun message) (fun result => (result.checkCalls : ENNReal)) ≤
      checkCalls

/-- **5. Binding** ([CY24, Lemma 18.4.1]): for every adversary and every `q ≥ 1`, the probability
that the adversary makes at most `q` permutation calls *and* wins the binding game is at most
`q / 2 ^ SECURITY_BITS`.

- There is no bound on the adversary's computation or private randomness; only its calls to `π`
  and `π⁻¹` count, not those `check` makes on its output.
- The event "at most `q` calls" sits inside the probability, so adversaries whose number of calls
  depends on the coins and on `π` are covered.
- An adversary making no calls is covered by `q = 1`: it wins with probability at most
  `2 ^ -SECURITY_BITS`, including by luck in `check`'s own calls.
- Equivalently, a scheme with binding error `ε(q)` qualifies when `q / ε(q) ≥ 2 ^ SECURITY_BITS`
  for every `q ∈ [1, 2 ^ SECURITY_BITS]`; for larger `q` the bound exceeds `1` and holds
  trivially. -/
def Binding : Prop :=
  ∀ (adversary : Adversary) (q : Nat), 1 ≤ q →
    Pr[fun (π, claim, calls) => scheme.Breaks π claim ∧ calls ≤ q | bindingGame adversary] ≤
      (q : ENNReal) / 2 ^ SECURITY_BITS

end Scheme

/-- **The competition claim.** `scheme` satisfies all five statements, and its scores are at most
`(proofBytes, checkCalls)`. Lower is better in both; the leaderboard is their Pareto frontier. -/
structure Certificate (scheme : Scheme) (proofBytes checkCalls : Nat) : Prop where
  completeness : scheme.Completeness
  honestBudgets : scheme.HonestBudgets
  proofSize : scheme.ProofSize proofBytes
  verificationCost : scheme.VerificationCost checkCalls
  binding : scheme.Binding

end CommitGolf
