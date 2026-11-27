import Lean.Elab.Tactic.Omega

/-! # Work and span of executed fork trees

Fork-mode instruction steps contribute sequential vertices. A binary fork contributes
a charged launch, two child traces, a charged join, and the parent's continuation.
Legacy execution is represented by one aggregate step. These are costs of the specified
abstract machine, not wall-clock time on a fixed processor count. The concrete executor
constructs the trace; submissions cannot supply a DAG.
-/

namespace CommitGolfDepth.Span.SpanMachine

inductive Trace where
  | done
  | step (cost queries : Nat) (next : Trace)
  | fork (launch join : Nat) (left right next : Trace)
  deriving DecidableEq

def Trace.work : Trace → Nat
  | .done => 0
  | .step c _ next => c + next.work
  | .fork launch join left right next => launch + left.work + right.work + join + next.work

def Trace.span : Trace → Nat
  | .done => 0
  | .step c _ next => c + next.span
  | .fork launch join left right next => launch + max left.span right.span + join + next.span

def Trace.queries : Trace → Nat
  | .done => 0
  | .step _ q next => q + next.queries
  | .fork _ _ left right next => left.queries + right.queries + next.queries

/-- Guest instructions attempted in an actual fork-machine trace. Zero-cost terminal
markers are not instructions; launch is the FORK instruction and join is model metadata.
The compressed legacy meter is excluded from instruction-exactness claims. -/
def Trace.instructions : Trace → Nat
  | .done => 0
  | .step c _ next => (if c = 0 then 0 else 1) + next.instructions
  | .fork _ _ left right next => 1 + left.instructions + right.instructions + next.instructions

theorem Trace.span_le_work (t : Trace) : t.span ≤ t.work := by
  induction t with
  | done => exact Nat.le_refl 0
  | step c q next ih => simp only [span, work]; omega
  | fork launch join left right next hl hr hn =>
    simp only [span, work]
    have hmax : max left.span right.span ≤ left.work + right.work := by omega
    omega

@[simp] theorem Trace.fork_work (launch join : Nat) (left right next : Trace) :
    (Trace.fork launch join left right next).work =
      launch + left.work + right.work + join + next.work := rfl

@[simp] theorem Trace.fork_span (launch join : Nat) (left right next : Trace) :
    (Trace.fork launch join left right next).span =
      launch + max left.span right.span + join + next.span := rfl

end CommitGolfDepth.Span.SpanMachine
