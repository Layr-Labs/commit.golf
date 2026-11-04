import CommitGolf.Binding
import CommitGolf.Hiding
import CommitGolf.Programs

/-! # Statements

The certificate checks the submitted machine programs and their derived scheme.
Honest-run bounds hold for every fixed oracle realization, message, and applicable set
of positions, with probability one over private coins. Probabilities live in `ENNReal`. -/

namespace CommitGolf
open OracleComp

namespace Scheme
variable (scheme : Scheme)

/-- **1. Completeness** [CY24, Lemma 18.2.1], perfect: `check` accepts the honest opening. -/
def Completeness : Prop :=
  ∀ (π : Oracle) (message : Message) (positions : Positions),
    Pr{let result ← scheme.honest π message positions}[result.accepted = true] = 1

/-- **2. Honest budgets.** -/
def HonestBudgets : Prop :=
  ∀ (π : Oracle) (message : Message) (positions : Positions),
    Pr{let result ← scheme.honest π message positions}[result.commitCalls ≤ COMMIT_BUDGET ∧
        result.openCalls ≤ OPEN_BUDGET positions.card ∧
        result.checkCalls ≤ CHECK_BUDGET positions.card] = 1

/-- **3. Proof size**, the byte bound used by the score, on openings of exactly `BATCH` positions. -/
def ProofSize (proofBytes : Nat) : Prop :=
  ∀ (π : Oracle) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr{let result ← scheme.honest π message positions}[result.proofBytes ≤ proofBytes] = 1

/-- **5. Position binding** [CY24, Lemma 18.4.1], without an extractor contract. -/
def Binding : Prop :=
  ∀ (adversary : Adversary) (q : Nat), 1 ≤ q →
    Pr{let (π, claim, calls) ← bindingGame adversary}[scheme.Breaks π claim ∧ calls ≤ q] ≤
      (q : ENNReal) / 2 ^ BINDING_SECURITY_BITS

/-- **6. Hiding**, a two-message formulation of commitment-and-opening privacy
(cf. [CY24, Lemma 18.6.3]). The adversary chooses two messages agreeing at the opened positions.
Honest commitment and opening of either message must give close adversary-output distributions,
for every fixed opening cardinality and total public-query budget across both adversary stages.
The cardinality is fixed outside the adversary's computation; positions precede commitment.
This states statistical indistinguishability, without a separate efficient-simulator claim. -/
def Hiding (error : Nat → Nat → ℝ) : Prop :=
  (∀ openingSize queryBudget, 0 ≤ error openingSize queryBudget) ∧
  ∀ (openingSize queryBudget : Nat),
    openingSize ≤ LENGTH →
    ∀ (AdversaryState Output : Type)
      (adversary : Hiding.HidingAdversary AdversaryState Output openingSize),
      Hiding.QueryBound adversary queryBudget →
      letI : MeasurableSpace Output := ⊤
      measureTVDist
        (Hiding.runHiding (Hiding.hidingExperiment scheme adversary false))
        (Hiding.runHiding (Hiding.hidingExperiment scheme adversary true)) ≤
        error openingSize queryBudget

end Scheme

/-- Valid images, nonoverlapping aligned buffers, and bounded instruction fuel. -/
def Submission.Admission (submission : Submission) : Prop :=
  ∀ program,
    (submission.image program).Valid (submission.layout.buffers submission.sizes) ∧
    0 < submission.steps program ∧ submission.steps program ≤ STEP_LIMIT

/-- Honest commitment and opening must succeed for every message and opening size.
This excludes faults, exhausted fuel, and oversized opening outputs. -/
def Submission.MachineSuccess (submission : Submission) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    Pr{let result ← oracle.run (submission.honestMachine message positions)}[
      result.1.success = true] = 1

/-- Every program finishes (success or failure) within its supplied fuel, including on
adversarial inputs. This is an execution bound, not an asymptotic PPT claim. -/
def Submission.Termination (submission : Submission) : Prop :=
  ∀ (oracle : Oracle) (program : Program) (input : Input submission.sizes program),
    Pr{let result ← oracle.run (submission.run program input)}[
      result.1.exit ≠ Riscv.Exit.unfinished] = 1

/-- **4. Prover cycles.** Separate worst-case bounds for a full commitment and one
opening of exactly `BATCH` positions. The score uses their sum, not an average. -/
def Submission.ProverCycles (submission : Submission) (commitCycles openingCycles : Nat) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr{let result ← oracle.run (submission.honestMachine message positions)}[
      result.1.commitCycles ≤ commitCycles ∧ result.1.openingCycles ≤ openingCycles] = 1

/-- One complete certificate for the submitted images. Security and proof size apply to the
scheme derived from those same images; solvers cannot supply an unrelated abstract scheme.
The score is `(commitCycles + openingCycles) * proofBytes`. -/
structure Certificate (submission : Submission) (proofBytes commitCycles openingCycles : Nat) : Prop where
  admission : submission.Admission
  machineSuccess : submission.MachineSuccess
  termination : submission.Termination
  completeness : submission.scheme.Completeness
  honestBudgets : submission.scheme.HonestBudgets
  proofSize : submission.scheme.ProofSize proofBytes
  proverCycles : submission.ProverCycles commitCycles openingCycles
  binding : submission.scheme.Binding
  hidingProperty : submission.scheme.Hiding HIDING_ERROR

end CommitGolf
