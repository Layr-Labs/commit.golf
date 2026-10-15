import CommitGolf.Security

/-! Perfect completeness, position binding, and the benchmark opening-size objective. -/
namespace CommitGolf.VectorCommit

open OracleComp OracleComp.EvalDist

/-- **Completeness.** Every adaptive choice of vector and positions opens and checks. -/
def Submission.Completeness (submission : Submission) : Prop :=
  ∀ A : CompletenessAdversary submission,
    Pr[= true | withROM (completenessGame submission A)] = 1

/-- **Position binding.** An adversary inside `QUERY_BUDGET` hash calls forges with probability
at most `bindingError submission.bindingBits`. -/
noncomputable def Submission.Security (submission : Submission) : Prop :=
  ∀ A : BindingAdversary submission, AdversaryWithinBudget A →
    Pr[= true | withROM (bindingGame submission A)] ≤ bindingError submission.bindingBits

/-- **Opening size.** For every vector, the expected average byte length of `OPENING_SAMPLES`
uniform single-position openings is at most `submission.openingBytes`. -/
def Submission.OpeningSize (submission : Submission) : Prop :=
  ∀ messages : Fin VECTOR_LENGTH → Message,
    expectedValue (withROM (openingSample submission messages))
      (fun total => match total with
        | none => ⊤
        | some n => (n : ENNReal) / OPENING_SAMPLES) ≤ submission.openingBytes

/-- The machine representations must fit, be disjoint, and have positive bounded step limits. -/
def Submission.Admission (s : Submission) : Prop :=
  0 < MESSAGE_BYTES ∧ 0 < COMMITMENT_BYTES ∧ 0 < OPENING_SAMPLES ∧
  Riscv.MEMORY_BYTES < 2 ^ 64 ∧ VECTOR_LENGTH ≤ 2 ^ 64 ∧
  ∀ p, (s.image p).Valid (s.layout.buffers s.sizes) ∧
    0 < s.steps p ∧ s.steps p ≤ Riscv.CYCLE_LIMIT

/-- Every admitted input halts or rejects before the cycle limit, for every possible response
sequence (including fresh private coins), not merely honestly generated inputs. -/
def Submission.Termination (s : Submission) : Prop :=
  ∀ p (input : Input s.sizes p) (result : Riscv.Execution), result ∈ support (s.run p input) →
    result.exit ≠ .unfinished ∧ result.cycles < Riscv.CYCLE_LIMIT

/-- Completeness, position binding at `QUERY_BUDGET` queries, and the opening-size score. -/
structure Certificate (submission : Submission) : Prop where
  admission : submission.Admission
  termination : submission.Termination
  bindingBitsValid : MIN_BINDING_BITS ≤ submission.bindingBits
  completeness : submission.Completeness
  security : submission.Security
  openingSize : submission.OpeningSize

end CommitGolf.VectorCommit
