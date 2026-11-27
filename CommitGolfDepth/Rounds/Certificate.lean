import CommitGolfDepth.Rounds.Submission

/-! # Complete security and resource certificate for the rounds track

Batching changes the image interpreter, so security is stated for `submission.scheme`
above, never for an unrelated abstract scheme or the old `submission.core.scheme`.
All honest resource bounds are unconditional almost-sure bounds for each fixed
oracle, message and applicable positions. Oracle rounds do not measure CPU span.
-/

namespace CommitGolfDepth.Rounds

open CommitGolf CommitGolf.Riscv OracleComp

def Submission.Admission (submission : Submission) : Prop := submission.core.Admission

def Submission.MachineSuccess (submission : Submission) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    Pr{let result ← oracle.run (submission.honestMachine message positions)}[
      result.1.success = true] = 1

/-- Includes malicious trapdoors/proofs, successful/failing paths, and both modes. -/
def Submission.Termination (submission : Submission) : Prop :=
  ∀ (oracle : Oracle) (program : Program) (input : Input submission.core.sizes program),
    Pr{let result ← oracle.run (submission.run program input)}[
      result.1.result.exit ≠ .unfinished] = 1

def Submission.ProverCycles (submission : Submission) (commitCycles openingCycles : Nat) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr{let result ← oracle.run (submission.honestMachine message positions)}[
      result.1.commitCycles ≤ commitCycles ∧ result.1.openingCycles ≤ openingCycles] = 1

def Submission.RoundBounds (submission : Submission) (commitRounds openingRounds : Nat) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions), positions.card = BATCH →
    Pr{let result ← oracle.run (submission.honestMachine message positions)}[
      result.1.commitRounds ≤ commitRounds ∧ result.1.openingRounds ≤ openingRounds] = 1

/-- The full certificate, including actual-image security and both resource systems. -/
structure Certificate (submission : Submission)
    (proofBytes commitCycles openingCycles commitRounds openingRounds : Nat) : Prop where
  admission : submission.Admission
  machineSuccess : submission.MachineSuccess
  termination : submission.Termination
  completeness : submission.scheme.Completeness
  honestBudgets : submission.scheme.HonestBudgets
  proofSize : submission.scheme.ProofSize proofBytes
  proverCycles : submission.ProverCycles commitCycles openingCycles
  binding : submission.scheme.Binding
  hidingProperty : submission.scheme.Hiding HIDING_ERROR
  roundBounds : submission.RoundBounds commitRounds openingRounds

end CommitGolfDepth.Rounds
