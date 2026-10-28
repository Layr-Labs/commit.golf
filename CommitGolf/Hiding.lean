import CommitGolf.Scheme
import VCVio.EvalDist.TVDist
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
structure HidingAdversary (family : OracleFamily)
    (AdversaryState Output : Type) (openingSize : Nat) where
  choose : OracleComp family.world (HidingChallenge AdversaryState openingSize)
  observe : AdversaryState → Commitment → Proof → OracleComp family.world Output

/-- Instrument syntactic executions, counting public calls and giving private coins cost zero.
Support quantifies over every possible oracle reply, rather than a sampled average. -/
def counted {family : OracleFamily} {α : Type} (c : OracleComp family.world α) :
    OracleComp family.world (α × Nat) :=
  costDist c ⟨family.callCost⟩

/-- A shared budget for both stages. After a first-stage path costing `calls`, every second-stage
execution has at most `queryBudget - calls` queries, for every possible commitment and proof. Both the
first-stage count and the combined count are bounded explicitly. -/
def QueryBound {family : OracleFamily} {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : HidingAdversary family AdversaryState Output openingSize)
    (queryBudget : Nat) : Prop :=
  ∀ first ∈ support (counted adversary.choose), first.2 ≤ queryBudget ∧
    ∀ root proof, ∀ last ∈ support (counted (adversary.observe first.1.aux root proof)),
      first.2 + last.2 ≤ queryBudget

/-- Both experiments honestly commit and open. `false` selects the first message and `true`
selects the second; the adversary receives neither the selector nor the internal trapdoor. -/
def hidingExperiment (scheme : Scheme) {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : HidingAdversary scheme.oracles AdversaryState Output openingSize)
    (selectSecond : Bool) : OracleComp scheme.oracles.world Output := do
  let challenge ← adversary.choose
  let message := if selectSecond then challenge.message₁ else challenge.message₀
  let (root, trapdoor) ← scheme.commit message
  let proof ← scheme.opening trapdoor challenge.positions
  adversary.observe challenge.aux root proof

/-- Initialize once, then preserve oracle state throughout the whole experiment. Neither the
final cache nor query counters are observations. Works for finite and lazy oracle families. -/
def runHiding (scheme : Scheme) {Output : Type}
    (experiment : OracleComp scheme.oracles.world Output) : ProbComp Output := do
  let initial ← scheme.oracles.initialState
  let ((output, _), _) ← (scheme.oracles.runShared experiment).run initial
  return output

/-- Pinned VCVio computations lose no probability mass; distances below compare normalized
output distributions, without conditioning on successful execution. -/
theorem runHiding_no_failure (scheme : Scheme) {Output : Type}
    (experiment : OracleComp scheme.oracles.world Output) :
    Pr[⊥ | runHiding scheme experiment] = 0 := probFailure_eq_zero

end CommitGolf.Hiding
