import CommitGolfDepth.Rounds.Certificate

/-! # Exact transport of complete legacy certificates

The bridge applies only to the explicit all-legacy mode. It transports every old
security/termination/resource obligation and requires a separate proof of the
new round bounds. It cannot certify batched semantics using an old certificate.
-/

namespace CommitGolfDepth.Rounds

open CommitGolf CommitGolf.Riscv OracleComp OracleSpec

abbrev liftLegacy (result : Riscv.Execution) : RoundMachine.Execution :=
  ⟨result, result.oracleCalls⟩

theorem run_ofLegacy (core : CommitGolf.Submission) (program : Program)
    (input : Input core.sizes program) :
    (Submission.ofLegacy core).run program input = liftLegacy <$> core.run program input := by
  cases program with
  | commit => rfl
  | opening => rfl
  | check =>
      by_cases valid : input.proof.length ≤ core.sizes.proof
      · simp [Submission.run, CommitGolf.Submission.run, Submission.ofLegacy,
          RoundMachine.execute, valid]
      · simp [Submission.run, CommitGolf.Submission.run,
          RoundMachine.failed, liftLegacy, valid]

theorem scheme_ofLegacy (core : CommitGolf.Submission) :
    (Submission.ofLegacy core).scheme = core.scheme := by
  simp only [Submission.scheme, CommitGolf.Submission.scheme]
  congr 1
  · funext message
    rw [run_ofLegacy core .commit message, Functor.map_map]
  · funext trapdoor positions
    rw [run_ofLegacy core .opening (trapdoor, positions), Functor.map_map]
  · funext root positions values proof
    rw [run_ofLegacy core .check ⟨root, positions, values, proof⟩,
      simulateQ_map, Functor.map_map]

theorem honestMachine_ofLegacy (core : CommitGolf.Submission) (message : Message)
    (positions : Positions) :
    MachineResult.toMachineResult <$> (Submission.ofLegacy core).honestMachine message positions =
      core.honestMachine message positions := by
  simp only [Submission.honestMachine, CommitGolf.Submission.honestMachine]
  rw [map_bind, run_ofLegacy core .commit message, bind_map_left]
  apply bind_congr
  intro committed
  rw [map_bind, run_ofLegacy core .opening ((core.readCommit committed).2, positions),
    bind_map_left]
  apply bind_congr
  intro opened
  simp only [map_pure]

theorem oracle_run_map (oracle : Oracle) {α β : Type} (f : α → β)
    (computation : OracleComp World α) :
    oracle.run (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> oracle.run computation := by
  simp only [Oracle.run, simulateQ_map, WriterT.run_map]
  rfl

theorem honestEvent_ofLegacy (core : CommitGolf.Submission) (oracle : Oracle)
    (message : Message) (positions : Positions) (event : CommitGolf.MachineResult → Prop) :
    Pr{let result ← oracle.run ((Submission.ofLegacy core).honestMachine message positions)}[
      event result.1.toMachineResult] =
      Pr{let result ← oracle.run (core.honestMachine message positions)}[event result.1] := by
  rw [← honestMachine_ofLegacy core message positions, oracle_run_map, prEvent_map]

/-- All old fields are transported; the independently proved new bound is mandatory. -/
theorem Certificate.ofLegacy (core : CommitGolf.Submission)
    (proofBytes commitCycles openingCycles commitRounds openingRounds : Nat)
    (certificate : CommitGolf.Certificate core proofBytes commitCycles openingCycles)
    (roundBounds : (Submission.ofLegacy core).RoundBounds commitRounds openingRounds) :
    Certificate (Submission.ofLegacy core) proofBytes commitCycles openingCycles commitRounds openingRounds where
  admission := certificate.admission
  machineSuccess := by
    intro oracle message positions
    rw [honestEvent_ofLegacy core oracle message positions (fun result => result.success = true)]
    exact certificate.machineSuccess oracle message positions
  termination := by
    intro oracle program input
    rw [run_ofLegacy core program input, oracle_run_map, prEvent_map]
    exact certificate.termination oracle program input
  completeness := by rw [scheme_ofLegacy]; exact certificate.completeness
  honestBudgets := by rw [scheme_ofLegacy]; exact certificate.honestBudgets
  proofSize := by rw [scheme_ofLegacy]; exact certificate.proofSize
  proverCycles := by
    intro oracle message positions cardinality
    rw [honestEvent_ofLegacy core oracle message positions
      (fun result => result.commitCycles ≤ commitCycles ∧ result.openingCycles ≤ openingCycles)]
    exact certificate.proverCycles oracle message positions cardinality
  binding := by rw [scheme_ofLegacy]; exact certificate.binding
  hidingProperty := by rw [scheme_ofLegacy]; exact certificate.hidingProperty
  roundBounds := roundBounds

end CommitGolfDepth.Rounds
