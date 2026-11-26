import CommitGolfDepth.Span.Machine
import CommitGolf.Statements

/-! # Images and their actual fork-machine scheme

Mode is fixed per program and is part of the artifact-linked submission. Legacy mode
delegates to the old complete interpreter without masking or changed syscall behavior.
Fork mode always uses the guarded interpreter, including all descendants. The core's
layout and loading ABI is unchanged; it supplies actual input bytes, never a solver's
unpriced host-language computation.
-/

namespace CommitGolfDepth.Span
open CommitGolf OracleComp OracleSpec

structure Submission where
  core : CommitGolf.Submission
  modes : Program → SpanMachine.Mode

def Submission.ofLegacy (core : CommitGolf.Submission) : Submission := ⟨core, fun _ => .legacy⟩

def Submission.run (s : Submission) (p : Program) (input : Input s.core.sizes p) :
    OracleComp World SpanMachine.Result :=
  match s.modes p with
  | .legacy => SpanMachine.Result.ofLegacy <$> s.core.run p input
  | .forkJoin =>
    let valid := match p, input with
      | .check, input => decide (input.proof.length ≤ s.core.sizes.proof)
      | _, _ => true
    if valid then
      SpanMachine.execute (s.core.image p) (s.core.steps p) (s.core.initialState p input) (p != .check)
    else pure (SpanMachine.stop .failure Riscv.initialMachine)

def Submission.scheme (s : Submission) : Scheme where
  Trapdoor := BitVec (8 * s.core.sizes.trapdoor)
  commit message := (fun r => s.core.readCommit r.toExecution) <$> s.run .commit message
  opening trapdoor positions := (fun r => s.core.readProof r.toExecution) <$>
    s.run .opening (trapdoor, positions)
  check root positions values proof :=
    (fun r => r.exit == .success) <$>
      simulateQ checkHandler (s.run .check ⟨root, positions, values, proof⟩)

structure MachineResult extends CommitGolf.MachineResult where
  commitSpan : Nat
  openingSpan : Nat

def MachineResult.ofLegacy (r : CommitGolf.MachineResult) : MachineResult :=
  ⟨r, r.commitCycles, r.openingCycles⟩

def Submission.honestMachine (s : Submission) (message : Message) (positions : Positions) :
    OracleComp World MachineResult := do
  let committed ← s.run .commit message
  let (_, trapdoor) := s.core.readCommit committed.toExecution
  let opened ← s.run .opening (trapdoor, positions)
  return {
    success := committed.exit == Riscv.Exit.success && s.core.openingSucceeded opened.toExecution
    commitCycles := committed.work
    openingCycles := opened.work
    proofBytes := (s.core.readProof opened.toExecution).length
    commitSpan := committed.span
    openingSpan := opened.span }

end CommitGolfDepth.Span
