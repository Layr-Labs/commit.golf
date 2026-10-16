import CommitGolf.Binding

/-! # Statements

The five statements a certificate proves, in the order of `RULES.md`, and the certificate.
Statements 1–4 hold in the honest run for every `π`, message, and set of positions, with
probability `1` (for all coins). Probabilities live in `ENNReal`. -/

namespace CommitGolf
open OracleComp

namespace Scheme
variable (scheme : Scheme)

/-- **1. Completeness** [CY24, Lemma 18.2.1], perfect: `check` accepts the honest opening. -/
def Completeness : Prop :=
  ∀ (π : Perm) (message : Message) (positions : Positions),
    Pr[fun result => result.accepted = true | scheme.honest π message positions] = 1

/-- **2. Honest budgets.** -/
def HonestBudgets : Prop :=
  ∀ (π : Perm) (message : Message) (positions : Positions),
    Pr[fun result => result.commitCalls ≤ COMMIT_BUDGET ∧
        result.openCalls ≤ OPEN_BUDGET positions.card ∧
        result.checkCalls ≤ CHECK_BUDGET positions.card |
      scheme.honest π message positions] = 1

/-- **3. Proof size**, the first score, on openings of exactly `BATCH` positions. -/
def ProofSize (proofBytes : Nat) : Prop :=
  ∀ (π : Perm) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr[fun result => result.proofBytes ≤ proofBytes | scheme.honest π message positions] = 1

/-- **4. Verification cost**, the second score, on openings of exactly `BATCH` positions. -/
def VerificationCost (checkCalls : Nat) : Prop :=
  ∀ (π : Perm) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr[fun result => result.checkCalls ≤ checkCalls | scheme.honest π message positions] = 1

/-- **5. Binding** [CY24, Lemma 18.4.1]. The number of calls may depend on the coins and on `π`. -/
def Binding : Prop :=
  ∀ (adversary : Adversary) (q : Nat), 1 ≤ q →
    Pr[fun (π, claim, calls) => scheme.Breaks π claim ∧ calls ≤ q | bindingGame adversary] ≤
      (q : ENNReal) / 2 ^ SECURITY_BITS

end Scheme

/-- The competition claim: `scheme` satisfies the five statements with scores at most
`(proofBytes, checkCalls)`. -/
structure Certificate (scheme : Scheme) (proofBytes checkCalls : Nat) : Prop where
  completeness : scheme.Completeness
  honestBudgets : scheme.HonestBudgets
  proofSize : scheme.ProofSize proofBytes
  verificationCost : scheme.VerificationCost checkCalls
  binding : scheme.Binding

end CommitGolf
