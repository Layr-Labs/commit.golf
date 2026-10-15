import CommitGolf.Programs
import VCVio.OracleComp.QueryTracking.QueryBound

/-! Chapter 18 completeness and binding games, and the honest opening-size experiment. The adversary chooses the commitment and both
openings. Only its oracle calls are bounded; subsequent checks are uncharged. -/
namespace CommitGolf
namespace VectorCommit
open OracleComp OracleSpec
/-- Chapter 18, Lemma 18.2.1: choose the vector and subset before honest commitment. -/
abbrev CompletenessAdversary (s : Submission) :=
  OracleComp (World s.family) (MessageVector × Positions)

def completenessGame (s : Submission) (A : CompletenessAdversary s) :
    OracleComp (World s.family) Bool := do
  let (m, I) ← A
  let some (c, td) ← s.commit m | return false
  let some pf ← s.opening td I | return false
  s.check c I (fun i => m i.val) pf

/-- Failed honest execution has no size score; the certificate assigns it infinite cost. -/
def openingSample (s : Submission) (m : MessageVector) :
    OracleComp (World s.family) (Option Nat) := do
  let some (_, td) ← s.commit m | return none
  let mut total := 0
  for _ in List.range OPENING_SAMPLES do
    let bits ← liftM ($ᵗ BitVec VECTOR_LOG_LENGTH : ProbComp (BitVec VECTOR_LOG_LENGTH))
    let some pf ← s.opening td {bits.toFin} | return none
    total := total + pf.length
  return some total

/-- Two opening claims at possibly different subsets of one commitment. -/
structure BindingForgery (submission : Submission) where
  commitment : Commitment
  indices₀ : Finset (Fin VECTOR_LENGTH)
  values₀ : ∀ _ : indices₀, Message
  proof₀ : List Byte
  indices₁ : Finset (Fin VECTOR_LENGTH)
  values₁ : ∀ _ : indices₁, Message
  proof₁ : List Byte

/-- An adversary chooses its own commitment and both opening claims. -/
abbrev BindingAdversary (submission : Submission) :=
  OracleComp (World submission.family) (BindingForgery submission)

/-- Claims disagree on at least one common coordinate. -/
def BindingForgery.conflicts {submission : Submission} (f : BindingForgery submission) : Prop :=
  ∃ (i : Fin VECTOR_LENGTH) (h₀ : i ∈ f.indices₀) (h₁ : i ∈ f.indices₁),
    f.values₀ ⟨i, h₀⟩ ≠ f.values₁ ⟨i, h₁⟩

/-- Two valid proofs for one commitment must not disagree at a common index. -/
noncomputable def checkBindingForgery (submission : Submission) (f : BindingForgery submission) :
    OracleComp (World submission.family) Bool := by
  classical
  exact do
    let b₀ ← submission.check f.commitment f.indices₀ f.values₀ f.proof₀
    let b₁ ← submission.check f.commitment f.indices₁ f.values₁ f.proof₁
    return b₀ && b₁ && decide f.conflicts

/-- The position-binding game: the adversary speaks, then both openings are checked. -/
noncomputable def bindingGame (submission : Submission) (A : BindingAdversary submission) :
    OracleComp (World submission.family) Bool := do
  let f ← A
  checkBindingForgery submission f

/-- Pathwise bound on adversarial hash queries, not on the verifier's. -/
def AdversaryWithinBudget {submission : Submission} (A : BindingAdversary submission) : Prop :=
  A.IsQueryBoundP (isHashQuery (F := submission.family)) QUERY_BUDGET

/-- Adversary cost, then both honest checks on the same cache, uncharged. Result:
`(didForge, adversaryHashCalls)`. -/
noncomputable def bindingExperimentCounted (submission : Submission)
    (A : BindingAdversary submission) : ProbComp (Bool × Nat) :=
  (do
    let (f, q) ← (simulateQ (countedOracle submission.family) A).run
    let success ← simulateQ (romImpl submission.family) (checkBindingForgery submission f)
    return (success, Multiplicative.toAdd q)
    : StateT (QueryCache (hashSpec submission.family)) ProbComp (Bool × Nat)).run' ∅

end VectorCommit

end CommitGolf
