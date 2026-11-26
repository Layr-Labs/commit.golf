import CommitGolfDepth.Span.Certificate

/-! # Exact legacy certificate transport

Only an all-legacy submission uses this bridge. Its actual execution, security scheme,
and full certificate agree with the original challenge, with work = span = cycles.
This theorem cannot certify a fork-mode image from an old certificate.
-/

namespace CommitGolfDepth.Span
open CommitGolf OracleComp

@[ext] theorem Submission.ext (s t : Submission) (core : s.core = t.core)
    (modes : s.modes = t.modes) : s = t := by
  cases s
  cases t
  simp_all

theorem run_ofLegacy (core : CommitGolf.Submission) (p : Program) (input : Input core.sizes p) :
    (Submission.ofLegacy core).run p input = SpanMachine.Result.ofLegacy <$> core.run p input := rfl

theorem scheme_ofLegacy (core : CommitGolf.Submission) :
    (Submission.ofLegacy core).scheme = core.scheme := by
  simp only [Submission.scheme, CommitGolf.Submission.scheme]
  congr 1
  · funext message
    rw [run_ofLegacy core .commit message, Functor.map_map]
    rfl
  · funext trapdoor positions
    let openingInput : Input core.sizes .opening := (trapdoor, positions)
    change (fun r => core.readProof r.toExecution) <$>
        (Submission.ofLegacy core).run .opening openingInput =
      core.readProof <$> core.run .opening openingInput
    rw [run_ofLegacy core .opening openingInput, Functor.map_map]
    rfl
  · funext root positions values proof
    rw [run_ofLegacy core .check ⟨root, positions, values, proof⟩,
      simulateQ_map, Functor.map_map]
    rfl

theorem honestMachine_ofLegacy (core : CommitGolf.Submission) (message : Message)
    (positions : Positions) :
    (Submission.ofLegacy core).honestMachine message positions =
      MachineResult.ofLegacy <$> core.honestMachine message positions := by
  simp only [Submission.honestMachine, CommitGolf.Submission.honestMachine]
  rw [map_bind, run_ofLegacy core .commit message, bind_map_left]
  apply bind_congr
  intro committed
  rw [map_bind]
  let openingInput : Input core.sizes .opening := ((core.readCommit committed).2, positions)
  change (do
      let opened ← (Submission.ofLegacy core).run .opening openingInput
      pure ({ success := committed.exit == Riscv.Exit.success && core.openingSucceeded opened.toExecution
              commitCycles := committed.cycles
              openingCycles := opened.work
              proofBytes := (core.readProof opened.toExecution).length
              commitSpan := committed.cycles
              openingSpan := opened.span } : MachineResult)) =
    (do
      let opened ← core.run .opening openingInput
      MachineResult.ofLegacy <$> pure
        ({ success := committed.exit == Riscv.Exit.success && core.openingSucceeded opened
           commitCycles := committed.cycles
           openingCycles := opened.cycles
           proofBytes := (core.readProof opened).length } : CommitGolf.MachineResult))
  rw [run_ofLegacy core .opening openingInput, bind_map_left]
  apply bind_congr
  intro opened
  simp only [map_pure]
  rfl

theorem oracle_run_map (oracle : Oracle) {α β : Type} (f : α → β)
    (computation : OracleComp World α) :
    oracle.run (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> oracle.run computation := by
  simp only [Oracle.run, simulateQ_map, WriterT.run_map]
  rfl

theorem honestEvent_ofLegacy (core : CommitGolf.Submission) (oracle : Oracle)
    (message : Message) (positions : Positions) (event : MachineResult → Prop) :
    Pr{let result ← oracle.run ((Submission.ofLegacy core).honestMachine message positions)}[
      event result.1] =
      Pr{let result ← oracle.run (core.honestMachine message positions)}[
        event (MachineResult.ofLegacy result.1)] := by
  rw [honestMachine_ofLegacy, oracle_run_map, prEvent_map]

theorem Certificate.ofLegacy (core : CommitGolf.Submission)
    (proofBytes commitWork openingWork : Nat)
    (certificate : CommitGolf.Certificate core proofBytes commitWork openingWork) :
    Certificate (Submission.ofLegacy core) proofBytes commitWork openingWork commitWork openingWork where
  admission := certificate.admission
  machineSuccess := by
    intro oracle message positions
    rw [honestEvent_ofLegacy core oracle message positions (fun result => result.success = true)]
    exact certificate.machineSuccess oracle message positions
  termination := by
    intro oracle p input
    rw [run_ofLegacy core p input, oracle_run_map, prEvent_map]
    exact certificate.termination oracle p input
  completeness := by rw [scheme_ofLegacy]; exact certificate.completeness
  honestBudgets := by rw [scheme_ofLegacy]; exact certificate.honestBudgets
  proofSize := by rw [scheme_ofLegacy]; exact certificate.proofSize
  proverWork := by
    intro oracle message positions cardinality
    rw [honestEvent_ofLegacy core oracle message positions
      (fun result => result.commitCycles ≤ commitWork ∧ result.openingCycles ≤ openingWork)]
    exact certificate.proverCycles oracle message positions cardinality
  proverSpan := by
    intro oracle message positions cardinality
    rw [honestEvent_ofLegacy core oracle message positions
      (fun result => result.commitSpan ≤ commitWork ∧ result.openingSpan ≤ openingWork)]
    exact certificate.proverCycles oracle message positions cardinality
  binding := by rw [scheme_ofLegacy]; exact certificate.binding
  hidingProperty := by rw [scheme_ofLegacy]; exact certificate.hidingProperty

end CommitGolfDepth.Span
