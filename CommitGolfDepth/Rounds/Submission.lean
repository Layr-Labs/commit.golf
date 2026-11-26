import CommitGolfDepth.Rounds.RoundMachine
import CommitGolf.Statements

/-! # Image-derived submissions for oracle-round accounting

Every phase selects an explicit, artifact-linked execution mode. In particular,
the scheme below is derived from the selected interpreter, not from `core.scheme`
when a program uses batching. The checker still cannot obtain private coins.
-/

namespace CommitGolfDepth.Rounds

open CommitGolf CommitGolf.Riscv OracleComp OracleSpec RiscvZkvm.Rv64

structure Submission where
  core : CommitGolf.Submission
  modes : Program → RoundMachine.Mode

abbrev Submission.ofLegacy (core : CommitGolf.Submission) : Submission :=
  ⟨core, fun _ => .legacy⟩

/-- Preserve the old ABI's rejection before loading an oversized supplied proof. -/
def Submission.run (submission : Submission) (program : Program)
    (input : Input submission.core.sizes program) : OracleComp World RoundMachine.Execution :=
  let valid := match program, input with
    | .check, input => decide (input.proof.length ≤ submission.core.sizes.proof)
    | _, _ => true
  if valid then
    RoundMachine.execute (submission.modes program) (submission.core.image program)
      (submission.core.steps program) (submission.core.initialState program input) (program != .check)
  else pure (RoundMachine.failed initialMachine 0)

/-- All security definitions use this actual mode-selected machine computation. -/
def Submission.scheme (submission : Submission) : Scheme where
  Trapdoor := BitVec (8 * submission.core.sizes.trapdoor)
  commit message :=
    (fun result => submission.core.readCommit result.result) <$> submission.run .commit message
  opening trapdoor positions :=
    (fun result => submission.core.readProof result.result) <$>
      submission.run .opening (trapdoor, positions)
  check root positions values proof :=
    (fun result => result.result.exit == .success) <$>
      simulateQ checkHandler (submission.run .check ⟨root, positions, values, proof⟩)

structure MachineResult extends CommitGolf.MachineResult where
  commitRounds : Nat
  openingRounds : Nat

/-- One full commitment, followed by one opening of its serialized trapdoor. -/
def Submission.honestMachine (submission : Submission) (message : Message)
    (positions : Positions) : OracleComp World MachineResult := do
  let committed ← submission.run .commit message
  let (_, trapdoor) := submission.core.readCommit committed.result
  let opened ← submission.run .opening (trapdoor, positions)
  return {
    success := committed.result.exit == .success && submission.core.openingSucceeded opened.result
    commitCycles := committed.result.cycles
    openingCycles := opened.result.cycles
    proofBytes := (submission.core.readProof opened.result).length
    commitRounds := committed.oracleRounds
    openingRounds := opened.oracleRounds }

end CommitGolfDepth.Rounds
