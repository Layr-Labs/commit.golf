import CommitGolf.Scheme
import VCVio.EvalDist.MeasureTVDist.Basic
import VCVio.OracleComp.QueryTracking.CostModel

/-! # Commitment and opening hiding

Two-message statistical hiding for a commitment and one opening. Each adversary has a
fixed opening cardinality. It chooses messages and positions before commitment, possibly
using oracle replies; the messages must agree at every opened position. `Scheme.Hiding`
in Statements.lean bounds the distance between its output distributions.

This ordering follows [CY24 v1.2, Lemma 18.6.3][cy24-hiding]. CY24 uses a variable-input
random oracle and a polynomial-time simulator; here the oracles are the fixed compression/
permutation pair, the views are honest, and the target error is uniform in cardinality.

Informally, in this same shared-oracle model with the same first-stage state, a simulator
can honestly commit and open the disclosed entries with zeros elsewhere, with the same
error. Conversely, a common simulator within δ of both views gives distance at most
min(1, 2δ). Neither reduction is formalized here. Full honest computation does not establish
an efficient simulator; transferring to CY24 also needs oracle-model and resource proofs.

CY24's Fiat–Shamir applications ([§22.2][cy24-micali], [§26.2][cy24-bcs]) use hybrids that
decouple positions from the root, with additional programming and bad-event errors. Those
arguments, post-commitment positions and repeated-opening privacy are not certified here.
One adversary choosing its cardinality from oracle replies is also outside this interface.
A generic reduction sums errors over at most `LENGTH + 1` sizes, capped at one: a proof
loss, not an attack.

[cy24-hiding]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.pdf#page=229
[cy24-micali]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.pdf#page=267
[cy24-bcs]: https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.pdf#page=313
-/

namespace CommitGolf.Hiding
open OracleComp OracleSpec

/-- One selected opening of exactly `openingSize` positions,
and the adversary's private retained state. -/
structure HidingChallenge (AdversaryState : Type) (openingSize : Nat) where
  message₀ : Message
  message₁ : Message
  positions : Positions
  size_eq : positions.card = openingSize
  agree : message₀.restrict positions = message₁.restrict positions
  aux : AdversaryState

/-- Both stages have private coins and public oracle access.
`AdversaryState` may retain the full message.
The output is any discrete observation, not the internal oracle state. -/
structure HidingAdversary
    (AdversaryState Output : Type) (openingSize : Nat) where
  choose : OracleComp World (HidingChallenge AdversaryState openingSize)
  observe : AdversaryState → Commitment → Proof → OracleComp World Output

/-- Instrument syntactic executions, counting public calls and giving private coins cost zero.
Support quantifies over every possible oracle reply, rather than a sampled average. -/
def counted {α : Type} (c : OracleComp World α) :
    OracleComp World (α × Nat) :=
  costDist c ⟨Oracle.callCost⟩

/-- A shared budget for both stages. After a first-stage path costing `calls`, every second-stage
execution has at most `queryBudget - calls` queries, for every possible commitment and proof. Both the
first-stage count and the combined count are bounded explicitly. -/
def QueryBound {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : HidingAdversary AdversaryState Output openingSize)
    (queryBudget : Nat) : Prop :=
  ∀ first ∈ support (counted adversary.choose), first.2 ≤ queryBudget ∧
    ∀ root proof, ∀ last ∈ support (counted (adversary.observe first.1.aux root proof)),
      first.2 + last.2 ≤ queryBudget

/-- Both experiments honestly commit and open. `false` selects the first message and `true`
selects the second; the adversary receives neither the selector nor the internal trapdoor. -/
def hidingExperiment (scheme : Scheme) {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : HidingAdversary AdversaryState Output openingSize)
    (selectSecond : Bool) : OracleComp World Output := do
  let challenge ← adversary.choose
  let message := if selectSecond then challenge.message₁ else challenge.message₀
  let (root, trapdoor) ← scheme.commit message
  let proof ← scheme.opening trapdoor challenge.positions
  adversary.observe challenge.aux root proof

/-- Sample the functions once for the whole experiment. Query counts and the functions
are not exposed in the adversary's observation. -/
def runHiding {Output : Type}
    (experiment : OracleComp World Output) : ProbComp Output := do
  let oracle ← Oracle.sample
  let (output, _) ← oracle.run experiment
  return output

/-- Pinned VCVio computations lose no probability mass; distances below compare normalized
output distributions, without conditioning on successful execution. -/
theorem runHiding_no_failure {Output : Type}
    (experiment : OracleComp World Output) :
    prFail (runHiding experiment) = 0 := OracleComp.prFail_eq_zero _

end CommitGolf.Hiding
