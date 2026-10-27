import CommitGolf.Binding
import CommitGolf.Hiding

/-! # Statements

The base certificate proves statements 1–5. Hiding certificates additionally prove statement 6.
Statements 1–4 hold in the honest run for every fixed oracle realization `π`, message, and set of positions, with
probability `1` (for all coins). Probabilities live in `ENNReal`. -/

namespace CommitGolf
open OracleComp
open PFunctor PFunctor.DynSystem.DynComputation

section HidingEnvironment

/- Public choices fixed by the challenge author: the parameter family, its challenge instance,
and VCVio's computational model, encodings, and resource policy. -/
variable (scheme : Scheme)
    (parameters : Nat → Hiding.HidingParameters) (challengeParameter : Nat)
    (atChallenge : parameters challengeParameter = Hiding.parametersOfScheme scheme)
    {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq (Hiding.HidingFamilySpec parameters).Domain]
    (costModel : QuantitativeStepClass C)
    (boundary : Boundary C (Hiding.HidingFamilySpec parameters).toPFunctor
      (SecurityFamily.Input (fun n => Hiding.SimulatorInput (parameters n)))
      (SecurityFamily.Output (fun n => Hiding.SimulatorOutput (parameters n))))
    {label : Type} (resources : Complexity.OracleContract costModel boundary.interface label)

namespace Scheme

/-- **1. Completeness** [CY24, Lemma 18.2.1], perfect: `check` accepts the honest opening. -/
def Completeness : Prop :=
  ∀ (π : scheme.oracles.Realization) (message : Message) (positions : Positions),
    Pr[fun result => result.accepted = true | scheme.honest π message positions] = 1

/-- **2. Honest budgets.** -/
def HonestBudgets : Prop :=
  ∀ (π : scheme.oracles.Realization) (message : Message) (positions : Positions),
    Pr[fun result => result.commitCalls ≤ COMMIT_BUDGET ∧
        result.openCalls ≤ OPEN_BUDGET positions.card ∧
        result.checkCalls ≤ CHECK_BUDGET positions.card |
      scheme.honest π message positions] = 1

/-- **3. Proof size**, the first score, on openings of exactly `BATCH` positions. -/
def ProofSize (proofBytes : Nat) : Prop :=
  ∀ (π : scheme.oracles.Realization) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr[fun result => result.proofBytes ≤ proofBytes | scheme.honest π message positions] = 1

/-- **4. Verification cost**, the second score, on openings of exactly `BATCH` positions. -/
def VerificationCost (checkCalls : Nat) : Prop :=
  ∀ (π : scheme.oracles.Realization) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr[fun result => result.checkCalls ≤ checkCalls | scheme.honest π message positions] = 1

/-- **5. Binding** [CY24, Lemma 18.4.1]. -/
def Binding : Prop :=
  ∀ (adversary : Adversary scheme.oracles) (q : Nat), 1 ≤ q →
    Pr[fun (claim, calls, a₀, a₁) => claim.Conflicting ∧ calls ≤ q ∧ a₀ = true ∧ a₁ = true | do
        let (π, claim, calls) ← bindingGame adversary
        let ((a₀, a₁), _) ← (scheme.checkClaim claim).run π
        return (claim, calls, a₀, a₁)] ≤
      (q : ENNReal) / 2 ^ SECURITY_BITS

/-- **6. Hiding** [CY24, Lemma 18.6.3]. The commitment and opening proof can be simulated
using only the opened positions and their values. For every query-bounded adversary, the real
and simulated experiments are within `error openingSize queryBudget` in statistical distance.
One simulator family must satisfy both this bound and VCVio's uniform, backend-relative PPT
requirement. -/
def Hiding (error : Nat → Nat → ℝ) : Prop :=
  ∃ simulatorFamily : Hiding.HidingSimulatorFamily parameters,
    Complexity.SecurityFamily.IsOraclePPTBy costModel boundary resources simulatorFamily ∧
    (∀ openingSize queryBudget, 0 ≤ error openingSize queryBudget) ∧
    ∀ (openingSize queryBudget : Nat),
      openingSize ≤ LENGTH →
      ∀ (AdversaryState Output : Type)
        (adversary : Hiding.HidingAdversary scheme.oracles AdversaryState Output openingSize),
        Hiding.QueryBound adversary queryBudget →
        tvDist
          (Hiding.runHiding scheme (Hiding.realHidingExperiment scheme adversary))
          (Hiding.runHiding scheme
            (Hiding.idealHidingExperiment scheme
              (Hiding.specialize simulatorFamily scheme challengeParameter atChallenge)
              adversary)) ≤
          error openingSize queryBudget

end Scheme

/-- Completeness, binding, and the honest resource bounds (statements 1–5). -/
structure Certificate (scheme : Scheme) (proofBytes checkCalls : Nat) : Prop where
  completeness : scheme.Completeness
  honestBudgets : scheme.HonestBudgets
  proofSize : scheme.ProofSize proofBytes
  verificationCost : scheme.VerificationCost checkCalls
  binding : scheme.Binding

/-- The base certificate plus commitment-and-opening hiding (statement 6). -/
structure HidingCertificate (proofBytes checkCalls : Nat) (error : Nat → Nat → ℝ) : Prop
    extends Certificate scheme proofBytes checkCalls where
  hidingProperty : scheme.Hiding parameters challengeParameter atChallenge costModel boundary resources error

/-- A binding-only track additionally restricts the declared oracle model. -/
abbrev TrackCertificate (track : Track) (scheme : Scheme) (proofBytes checkCalls : Nat) : Prop :=
  Certificate scheme proofBytes checkCalls ∧ scheme.oracles.InTrack track

/-! ### Named track certificates

Import `CommitGolf.Statements` for these complete submission requirements. Non-hiding tracks
require the base certificate and oracle membership. Hiding tracks add `HIDING_ERROR` and PPT simulation.
The hiding environment remains explicit for the challenge author to fix, not the solver.
-/

abbrev IdealPermutationCertificate (scheme : Scheme) (proofBytes checkCalls : Nat) : Prop :=
  TrackCertificate .idealPermutation scheme proofBytes checkCalls

abbrev IdealCompressionCertificate (scheme : Scheme) (proofBytes checkCalls : Nat) : Prop :=
  TrackCertificate .idealCompression scheme proofBytes checkCalls

abbrev RandomOracleFixedOutputCertificate (scheme : Scheme) (proofBytes checkCalls : Nat) : Prop :=
  TrackCertificate .randomOracleFixedOutput scheme proofBytes checkCalls

abbrev IdealXofCertificate (scheme : Scheme) (proofBytes checkCalls : Nat) : Prop :=
  TrackCertificate .idealXof scheme proofBytes checkCalls

variable (proofBytes checkCalls : Nat)

abbrev IdealPermutationHidingCertificate : Prop :=
  HidingCertificate scheme parameters challengeParameter atChallenge costModel boundary resources
    proofBytes checkCalls HIDING_ERROR ∧ scheme.oracles.InTrack .idealPermutation

abbrev IdealCompressionHidingCertificate : Prop :=
  HidingCertificate scheme parameters challengeParameter atChallenge costModel boundary resources
    proofBytes checkCalls HIDING_ERROR ∧ scheme.oracles.InTrack .idealCompression

abbrev RandomOracleFixedOutputHidingCertificate : Prop :=
  HidingCertificate scheme parameters challengeParameter atChallenge costModel boundary resources
    proofBytes checkCalls HIDING_ERROR ∧ scheme.oracles.InTrack .randomOracleFixedOutput

abbrev IdealXofHidingCertificate : Prop :=
  HidingCertificate scheme parameters challengeParameter atChallenge costModel boundary resources
    proofBytes checkCalls HIDING_ERROR ∧ scheme.oracles.InTrack .idealXof

end HidingEnvironment

end CommitGolf
