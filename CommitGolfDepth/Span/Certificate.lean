import CommitGolfDepth.Span.Submission

/-! # Complete certificate for work/span Pareto submissions

All games and honest bounds concern the same actual submitted images under their fixed
execution modes. Work is total charged instruction/fork work; span is weighted critical
path in the executed binary fork tree. It is neither oracle-query depth nor physical
multicore runtime. Checker cycles, context storage and input loading remain unscored.
-/

namespace CommitGolfDepth.Span
open CommitGolf OracleComp

def Submission.Admission (s : Submission) : Prop := s.core.Admission

def Submission.MachineSuccess (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    Pr{let result ← oracle.run (s.honestMachine message positions)}[result.1.success = true] = 1

def Submission.Termination (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (program : Program) (input : Input s.core.sizes program),
    Pr{let result ← oracle.run (s.run program input)}[result.1.exit ≠ .unfinished] = 1

def Submission.ProverWork (s : Submission) (commitWork openingWork : Nat) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr{let result ← oracle.run (s.honestMachine message positions)}[
      result.1.commitCycles ≤ commitWork ∧ result.1.openingCycles ≤ openingWork] = 1

def Submission.ProverSpan (s : Submission) (commitSpan openingSpan : Nat) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr{let result ← oracle.run (s.honestMachine message positions)}[
      result.1.commitSpan ≤ commitSpan ∧ result.1.openingSpan ≤ openingSpan] = 1

structure Certificate (submission : Submission)
    (proofBytes commitWork openingWork commitSpan openingSpan : Nat) : Prop where
  admission : submission.Admission
  machineSuccess : submission.MachineSuccess
  termination : submission.Termination
  completeness : submission.scheme.Completeness
  honestBudgets : submission.scheme.HonestBudgets
  proofSize : submission.scheme.ProofSize proofBytes
  proverWork : submission.ProverWork commitWork openingWork
  proverSpan : submission.ProverSpan commitSpan openingSpan
  binding : submission.scheme.Binding
  hidingProperty : submission.scheme.Hiding HIDING_ERROR

end CommitGolfDepth.Span
