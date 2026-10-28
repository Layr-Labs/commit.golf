import CommitGolf.Binding
import CommitGolf.Hiding

/-! # Statements

The submission certificate proves all six statements and fixes the available oracle pair.
Statements 1–4 hold in the honest run for every fixed oracle realization `π`, message, and set of positions, with
probability `1` (for all coins). Probabilities live in `ENNReal`. -/

namespace CommitGolf
open OracleComp

variable (scheme : Scheme)

namespace Scheme

/-- **1. Completeness** [CY24, Lemma 18.2.1], perfect: `check` accepts the honest opening. -/
def Completeness : Prop :=
  ∀ (π : Oracle) (message : Message) (positions : Positions),
    Pr[fun result => result.accepted = true | scheme.honest π message positions] = 1

/-- **2. Honest budgets.** -/
def HonestBudgets : Prop :=
  ∀ (π : Oracle) (message : Message) (positions : Positions),
    Pr[fun result => result.commitCalls ≤ COMMIT_BUDGET ∧
        result.openCalls ≤ OPEN_BUDGET positions.card ∧
        result.checkCalls ≤ CHECK_BUDGET positions.card |
      scheme.honest π message positions] = 1

/-- **3. Proof size**, the first score, on openings of exactly `BATCH` positions. -/
def ProofSize (proofBytes : Nat) : Prop :=
  ∀ (π : Oracle) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr[fun result => result.proofBytes ≤ proofBytes | scheme.honest π message positions] = 1

/-- **4. Verification cost**, the second score, on openings of exactly `BATCH` positions. -/
def VerificationCost (checkCalls : Nat) : Prop :=
  ∀ (π : Oracle) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr[fun result => result.checkCalls ≤ checkCalls | scheme.honest π message positions] = 1

/-- **5. Binding** [CY24, Lemma 18.4.1]. -/
def Binding : Prop :=
  ∀ (adversary : Adversary) (q : Nat), 1 ≤ q →
    Pr[fun (π, claim, calls) => scheme.Breaks π claim ∧ calls ≤ q |
      bindingGame adversary] ≤ (q : ENNReal) / 2 ^ SECURITY_BITS

/-- **6. Hiding**, a two-message formulation of commitment-and-opening privacy
(cf. [CY24, Lemma 18.6.3]). The adversary chooses two messages agreeing at the opened positions.
Honest commitment and opening of either message must give close adversary-output distributions,
for every opening size and total public-query budget across both adversary stages.
This states statistical indistinguishability, without a separate efficient-simulator claim. -/
def Hiding (error : Nat → Nat → ℝ) : Prop :=
  (∀ openingSize queryBudget, 0 ≤ error openingSize queryBudget) ∧
  ∀ (openingSize queryBudget : Nat),
    openingSize ≤ LENGTH →
    ∀ (AdversaryState Output : Type)
      (adversary : Hiding.HidingAdversary AdversaryState Output openingSize),
      Hiding.QueryBound adversary queryBudget →
      tvDist
        (Hiding.runHiding (Hiding.hidingExperiment scheme adversary false))
        (Hiding.runHiding (Hiding.hidingExperiment scheme adversary true)) ≤
        error openingSize queryBudget

end Scheme

/-- The complete submission certificate: correctness, binding, hiding, resource bounds,
and access to both fixed oracle primitives together. -/
structure Certificate (scheme : Scheme) (proofBytes checkCalls : Nat) : Prop where
  completeness : scheme.Completeness
  honestBudgets : scheme.HonestBudgets
  proofSize : scheme.ProofSize proofBytes
  verificationCost : scheme.VerificationCost checkCalls
  binding : scheme.Binding
  hidingProperty : scheme.Hiding HIDING_ERROR

end CommitGolf
