import CommitGolf.Scheme
import VCVio.EvalDist.MeasureTVDist.Basic
import VCVio.OracleComp.QueryTracking.CostModel

/-! # Commitment and opening hiding

Two-message statistical hiding for a commitment and one opening. The messages must agree at
all opened positions. Positions are chosen before the commitment, not adaptively afterwards.
`Scheme.Hiding` in Statements.lean bounds the distance between the two output distributions.
This formulation has no separate simulator or computational-complexity requirement.
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
