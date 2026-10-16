import CommitGolf.Binding

/-! # Statements

The five properties a submission proves, in the order `RULES.md` lists them, and the `Certificate`
bundling them. The certificate for a scheme and two claimed scores is the competition claim.

Statements 1–4 are worst-case: they hold with probability `1` in the honest run, for every
permutation, message, and set of positions (of exactly `BATCH` positions for the two scores), and
for all coins. Probabilities are valued in `ENNReal`, the nonnegative reals extended with `∞`. -/

namespace CommitGolf
open OracleComp

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
in the honest run `commit` makes at most `COMMIT_BUDGET` permutation calls, `opening` at most
`OPEN_BUDGET |I|`, and `check` at most `CHECK_BUDGET |I|`. Only honest openings are budgeted:
`check` may take any number of calls on other inputs. -/
def HonestBudgets : Prop :=
  ∀ (π : Perm) (message : Message) (positions : Positions),
    Pr[fun result => result.commitCalls ≤ COMMIT_BUDGET ∧
        result.openCalls ≤ OPEN_BUDGET positions.card ∧
        result.checkCalls ≤ CHECK_BUDGET positions.card |
      scheme.honest π message positions] = 1

/-- **3. Proof size**, the first score: for every permutation, message, set of exactly `BATCH`
positions, and for all coins, the honest opening proof has at most `proofBytes` bytes. -/
def ProofSize (proofBytes : Nat) : Prop :=
  ∀ (π : Perm) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr[fun result => result.proofBytes ≤ proofBytes | scheme.honest π message positions] = 1

/-- **4. Verification cost**, the second score: for every permutation, message, set of exactly
`BATCH` positions, and for all coins, `check` makes at most `checkCalls` permutation calls on the
honest opening. -/
def VerificationCost (checkCalls : Nat) : Prop :=
  ∀ (π : Perm) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr[fun result => result.checkCalls ≤ checkCalls | scheme.honest π message positions] = 1

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
