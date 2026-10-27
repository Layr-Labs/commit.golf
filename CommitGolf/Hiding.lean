import CommitGolf.Scheme
import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.QueryTracking.CostModel

/-! # Commitment and opening hiding

The real/simulated experiments of CY24, Lemma 18.6.3, generalized to the declared oracle family.
Positions are chosen before the commitment; this is one opening, not adaptive multiple openings.
Statistical hiding and backend-relative uniform PPT are separate obligations, combined in
`Scheme.Hiding`. Existing track certificates are unchanged. A concrete complexity backend
and parameter profile still need to be fixed before enabling hiding-track admission.
-/

namespace CommitGolf.Hiding
open OracleComp OracleSpec

/-- One selected opening of exactly `openingSize` positions,
and the adversary's private retained state. -/
structure HidingChallenge (AdversaryState : Type) (openingSize : Nat) where
  message : Message
  positions : Positions
  size_eq : positions.card = openingSize
  aux : AdversaryState

/-- Both stages have private coins and public oracle access.
`AdversaryState` may retain the full message.
The output is any discrete observation, not the internal oracle state. -/
structure HidingAdversary (family : OracleFamily)
    (AdversaryState Output : Type) (openingSize : Nat) where
  choose : OracleComp family.world (HidingChallenge AdversaryState openingSize)
  observe : AdversaryState → Commitment → Proof → OracleComp family.world Output

/-- Only the selected positions and values are supplied; public scheme parameters are fixed.
The simulator has ordinary oracle access, not access to the oracle cache or adversary state. -/
abbrev HidingSimulator (scheme : Scheme) :=
  (positions : Positions) → Values positions →
    OracleComp scheme.oracles.world (Commitment × Proof)

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

/-- Honest commitment followed by one opening and the adversary's observation. -/
def realHidingExperiment (scheme : Scheme) {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : HidingAdversary scheme.oracles AdversaryState Output openingSize) :
    OracleComp scheme.oracles.world Output := do
  let challenge ← adversary.choose
  let (root, trapdoor) ← scheme.commit challenge.message
  let proof ← scheme.opening trapdoor challenge.positions
  adversary.observe challenge.aux root proof

/-- Simulate the commitment and proof jointly from the opened values alone. -/
def idealHidingExperiment (scheme : Scheme) (simulate : HidingSimulator scheme)
    {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : HidingAdversary scheme.oracles AdversaryState Output openingSize) :
    OracleComp scheme.oracles.world Output := do
  let challenge ← adversary.choose
  let (root, proof) ← simulate challenge.positions
    (challenge.message.restrict challenge.positions)
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

/-- Statistical hiding for a specified simulator, with error indexed by opening size and the
adversary's total public-query budget. Discrete TV supports infinite discrete observation types
and connects directly to VCVio's identical-until-bad lemmas; infinite oracle domains need no
whole-function sampling here. A zero-sized opening is included. -/
def StatisticalHiding (scheme : Scheme) (simulate : HidingSimulator scheme)
    (error : Nat → Nat → ℝ) : Prop :=
  ∀ (openingSize queryBudget : Nat), openingSize ≤ LENGTH →
    ∀ (AdversaryState Output : Type)
      (adversary : HidingAdversary scheme.oracles AdversaryState Output openingSize),
      QueryBound adversary queryBudget →
      tvDist (runHiding scheme (realHidingExperiment scheme adversary))
        (runHiding scheme (idealHidingExperiment scheme simulate adversary)) ≤
        error openingSize queryBudget

/-- One simulator must work for all opening sizes, budgets, and adversaries. This is only a
statistical certificate, deliberately not the textbook's additional efficient-simulation claim. -/
structure StatisticalHidingCertificate (scheme : Scheme) (error : Nat → Nat → ℝ) where
  simulator : HidingSimulator scheme
  error_nonneg : ∀ openingSize queryBudget, 0 ≤ error openingSize queryBudget
  statistical : StatisticalHiding scheme simulator error

/-! # Uniform simulator efficiency

A fixed challenge instance alone cannot express asymptotic efficiency. A contract supplies a
parameter profile, an operational backend, encodings, and an oracle response-resource contract.
The simulator must have one uniform implementation for the whole profile. Its specialization at
the challenge parameter is exactly the simulator in the statistical hiding game.

`Scheme.Hiding` is backend-relative, as is VCVio's `IsOraclePPTBy`. It is not an unqualified
machine-model PPT theorem. The contract must pin suitable encodings (including the security
parameter, normally unary), a meaningful growing profile, and the backend's adequacy evidence
before using this certificate for admission. None are chosen existentially by the certificate.
-/

open PFunctor PFunctor.DynSystem.DynComputation

/-- Public dimensions and oracle declarations at one member of a simulator family. -/
structure HidingParameters where
  length : Nat
  entryBits : Nat
  commitmentBits : Nat
  oracles : OracleFamily

/-- The existing fixed-size challenge, without changing its scheme or binding definitions. -/
def parametersOfScheme (scheme : Scheme) : HidingParameters :=
  ⟨LENGTH, DIGEST_BITS, DIGEST_BITS, scheme.oracles⟩

/-- Only opened positions and values; no unopened entries or adversarial auxiliary state. -/
abbrev SimulatorInput (p : HidingParameters) :=
  (positions : Finset (Fin p.length)) × (positions → BitVec p.entryBits)

abbrev SimulatorOutput (p : HidingParameters) := BitVec p.commitmentBits × Proof

/-- The public profile is fixed by the contract. One program takes the parameter as input;
unrelated polynomial-time witnesses for each parameter are insufficient. -/
abbrev HidingSimulatorFamily (parameters : Nat → HidingParameters) :=
  (n : Nat) → SimulatorInput (parameters n) →
    OracleComp (parameters n).oracles.world (SimulatorOutput (parameters n))

/-- Specialization is equality transport only: no uncharged input/output adapter can insert
extra computation between the certified family and the simulator used in the game. -/
def specialize {parameters : Nat → HidingParameters}
    (simulatorFamily : HidingSimulatorFamily parameters) (scheme : Scheme) (n : Nat)
    (atChallenge : parameters n = parametersOfScheme scheme) : HidingSimulator scheme :=
  let member : SimulatorInput (parametersOfScheme scheme) →
      OracleComp scheme.oracles.world (SimulatorOutput (parametersOfScheme scheme)) :=
    Eq.mp (congrArg (fun p : HidingParameters =>
      SimulatorInput p → OracleComp p.oracles.world (SimulatorOutput p)) atChallenge)
      (simulatorFamily n)
  fun positions values => member ⟨positions, values⟩

/-- Aggregate interface: queries retain their parameter and their oracle-instance identity. -/
abbrev HidingFamilySpec (parameters : Nat → HidingParameters) :=
  SecurityFamily.Spec (fun n => (parameters n).oracles.world)

end CommitGolf.Hiding
