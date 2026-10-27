import CommitGolf.Scheme
import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.QueryTracking.CostModel

/-! # Commitment and opening hiding

The real/simulated experiments of CY24, Lemma 18.6.3, generalized to the declared oracle family.
Positions are chosen before the commitment; this is one opening, not adaptive multiple openings.
Statistical hiding and backend-relative uniform PPT are separate obligations, combined in
`HidingCertificateBy`. Existing track certificates are unchanged. A concrete complexity backend
and parameter profile still need to be fixed before enabling hiding-track admission.
-/

namespace CommitGolf
open OracleComp OracleSpec

/-- One selected opening of exactly `q` positions, and the adversary's private retained state. -/
structure HidingChallenge (Aux : Type) (q : Nat) where
  message : Message
  positions : Positions
  size_eq : positions.card = q
  aux : Aux

/-- Both stages have private coins and public oracle access. `Aux` may retain the full message.
The output is any discrete observation, not the internal oracle state. -/
structure HidingAdversary (family : OracleFamily) (Aux Output : Type) (q : Nat) where
  choose : OracleComp family.world (HidingChallenge Aux q)
  observe : Aux → Commitment → Proof → OracleComp family.world Output

/-- Only the selected positions and values are supplied; public scheme parameters are fixed.
The simulator has ordinary oracle access, not access to the oracle cache or adversary state. -/
abbrev HidingSimulator (scheme : Scheme) :=
  (positions : Positions) → Values positions →
    OracleComp scheme.oracles.world (Commitment × Proof)

namespace HidingAdversary

/-- Instrument syntactic executions, counting public calls and giving private coins cost zero.
Support quantifies over every possible oracle reply, rather than a sampled average. -/
def counted {family : OracleFamily} {α : Type} (c : OracleComp family.world α) :
    OracleComp family.world (α × Nat) :=
  costDist c ⟨family.callCost⟩

/-- A shared budget for both stages. After a first-stage path costing `calls`, every second-stage
execution has at most `t - calls` queries, for every possible commitment and proof. Both the
first-stage count and the combined count are bounded explicitly. -/
def QueryBound {family : OracleFamily} {Aux Output : Type} {q : Nat}
    (A : HidingAdversary family Aux Output q) (t : Nat) : Prop :=
  ∀ first ∈ support (counted A.choose), first.2 ≤ t ∧
    ∀ root proof, ∀ last ∈ support (counted (A.observe first.1.aux root proof)),
      first.2 + last.2 ≤ t

end HidingAdversary

namespace Scheme

/-- Honest commitment followed by one opening and the adversary's observation. -/
def realHidingExperiment (scheme : Scheme) {Aux Output : Type} {q : Nat}
    (A : HidingAdversary scheme.oracles Aux Output q) :
    OracleComp scheme.oracles.world Output := do
  let challenge ← A.choose
  let (root, trapdoor) ← scheme.commit challenge.message
  let proof ← scheme.opening trapdoor challenge.positions
  A.observe challenge.aux root proof

/-- Simulate the commitment and proof jointly from the opened values alone. -/
def idealHidingExperiment (scheme : Scheme) (simulate : HidingSimulator scheme)
    {Aux Output : Type} {q : Nat} (A : HidingAdversary scheme.oracles Aux Output q) :
    OracleComp scheme.oracles.world Output := do
  let challenge ← A.choose
  let (root, proof) ← simulate challenge.positions
    (challenge.message.restrict challenge.positions)
  A.observe challenge.aux root proof

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
    Pr[⊥ | scheme.runHiding experiment] = 0 := probFailure_eq_zero

/-- Statistical hiding for a specified simulator, with error indexed by opening size and the
adversary's total public-query budget. Discrete TV supports infinite discrete observation types
and connects directly to VCVio's identical-until-bad lemmas; infinite oracle domains need no
whole-function sampling here. A zero-sized opening is included. -/
def StatisticalHiding (scheme : Scheme) (simulate : HidingSimulator scheme)
    (error : Nat → Nat → ℝ) : Prop :=
  ∀ (q t : Nat), q ≤ LENGTH → ∀ (Aux Output : Type)
    (A : HidingAdversary scheme.oracles Aux Output q), A.QueryBound t →
      tvDist (scheme.runHiding (scheme.realHidingExperiment A))
        (scheme.runHiding (scheme.idealHidingExperiment simulate A)) ≤ error q t

/-- One simulator must work for all opening sizes, budgets, and adversaries. This is only a
statistical certificate, deliberately not the textbook's additional efficient-simulation claim. -/
structure StatisticalHidingCertificate (scheme : Scheme) (error : Nat → Nat → ℝ) where
  simulator : HidingSimulator scheme
  error_nonneg : ∀ q t, 0 ≤ error q t
  statistical : scheme.StatisticalHiding simulator error

end Scheme
end CommitGolf

/-! # Uniform simulator efficiency

A fixed challenge instance alone cannot express asymptotic efficiency. A contract supplies a
parameter profile, an operational backend, encodings, and an oracle response-resource contract.
The simulator must have one uniform implementation for the whole profile. Its specialization at
the challenge parameter is exactly the simulator in the statistical hiding game.

`HidingCertificateBy` is backend-relative, as is VCVio's `IsOraclePPTBy`. It is not an unqualified
machine-model PPT theorem. The contract must pin suitable encodings (including the security
parameter, normally unary), a meaningful growing profile, and the backend's adequacy evidence
before using this certificate for admission. None are chosen existentially by the certificate.
-/

namespace CommitGolf
open OracleComp OracleSpec
open PFunctor PFunctor.DynSystem.DynComputation

/-- Public dimensions and oracle declarations at one member of a simulator family. -/
structure HidingParameters where
  length : Nat
  entryBits : Nat
  commitmentBits : Nat
  oracles : OracleFamily

namespace HidingParameters

/-- The existing fixed-size challenge, without changing its scheme or binding definitions. -/
def ofScheme (scheme : Scheme) : HidingParameters :=
  ⟨LENGTH, DIGEST_BITS, DIGEST_BITS, scheme.oracles⟩

/-- Only opened positions and values; no unopened entries or adversarial auxiliary state. -/
abbrev Input (p : HidingParameters) :=
  (positions : Finset (Fin p.length)) × (positions → BitVec p.entryBits)

abbrev Output (p : HidingParameters) := BitVec p.commitmentBits × Proof

end HidingParameters

/-- The public profile is fixed by the contract. One program takes the parameter as input;
unrelated polynomial-time witnesses for each parameter are insufficient. -/
abbrev HidingSimulatorFamily (parameters : Nat → HidingParameters) :=
  (n : Nat) → (parameters n).Input →
    OracleComp (parameters n).oracles.world (parameters n).Output

namespace HidingSimulatorFamily

/-- Specialization is equality transport only: no uncharged input/output adapter can insert
extra computation between the certified family and the simulator used in the game. -/
def specialize {parameters : Nat → HidingParameters}
    (simulate : HidingSimulatorFamily parameters) (scheme : Scheme) (n : Nat)
    (atChallenge : parameters n = HidingParameters.ofScheme scheme) : HidingSimulator scheme :=
  let member : (HidingParameters.ofScheme scheme).Input →
      OracleComp scheme.oracles.world (HidingParameters.ofScheme scheme).Output :=
    Eq.mp (congrArg (fun p : HidingParameters =>
      p.Input → OracleComp p.oracles.world p.Output) atChallenge) (simulate n)
  fun positions values => member ⟨positions, values⟩

end HidingSimulatorFamily

/-- Aggregate interface: queries retain their parameter and their oracle-instance identity. -/
abbrev HidingFamilySpec (parameters : Nat → HidingParameters) :=
  SecurityFamily.Spec (fun n => (parameters n).oracles.world)

/-- The computational model, boundary encodings, resource policy, and parameter profile are
external contract arguments. The certificate supplies one simulator family, proves its uniform
strict PPT relative to those arguments, and proves hiding for that same family's specialization.

VCVio's witness includes semantic implementation, pathwise polynomial resource bounds, and
output-size recovery. It is not a query-count annotation. Public-oracle and private-randomness
response policies must both be covered by the pinned resource contract. -/
structure HidingCertificateBy
    (scheme : Scheme) (error : Nat → Nat → ℝ)
    (parameters : Nat → HidingParameters) (challengeParameter : Nat)
    (atChallenge : parameters challengeParameter = HidingParameters.ofScheme scheme)
    {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq (HidingFamilySpec parameters).Domain]
    (Q : QuantitativeStepClass C)
    (boundary : Boundary C (HidingFamilySpec parameters).toPFunctor
      (SecurityFamily.Input (fun n => (parameters n).Input))
      (SecurityFamily.Output (fun n => (parameters n).Output)))
    {label : Type} (resources : Complexity.OracleContract Q boundary.interface label) where
  simulators : HidingSimulatorFamily parameters
  ppt : Complexity.SecurityFamily.IsOraclePPTBy Q boundary resources simulators
  error_nonneg : ∀ q t, 0 ≤ error q t
  statistical : scheme.StatisticalHiding
    (simulators.specialize scheme challengeParameter atChallenge) error

namespace HidingCertificateBy

variable {scheme : Scheme} {error : Nat → Nat → ℝ}
  {parameters : Nat → HidingParameters} {challengeParameter : Nat}
  {atChallenge : parameters challengeParameter = HidingParameters.ofScheme scheme}
  {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq (HidingFamilySpec parameters).Domain]
  {Q : QuantitativeStepClass C}
  {boundary : Boundary C (HidingFamilySpec parameters).toPFunctor
    (SecurityFamily.Input (fun n => (parameters n).Input))
    (SecurityFamily.Output (fun n => (parameters n).Output))}
  {label : Type} {resources : Complexity.OracleContract Q boundary.interface label}

/-- Forget efficiency without changing the certified simulator or statistical claim. -/
def toStatistical (certificate : HidingCertificateBy scheme error parameters
    challengeParameter atChallenge Q boundary resources) :
    scheme.StatisticalHidingCertificate error where
  simulator := certificate.simulators.specialize scheme challengeParameter atChallenge
  error_nonneg := certificate.error_nonneg
  statistical := certificate.statistical

end HidingCertificateBy
end CommitGolf
