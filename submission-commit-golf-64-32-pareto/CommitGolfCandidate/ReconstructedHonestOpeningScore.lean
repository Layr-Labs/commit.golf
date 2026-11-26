import CommitGolfCandidate.ReconstructedHonestRecordExecution
import CommitGolfCandidate.ReconstructedHonestCapComplete
import CommitGolfCandidate.Machine

namespace CommitGolfCandidate.Reconstruction.HonestOpeningScore
open CommitGolf CommitGolf.Riscv OracleComp

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode execute

private theorem run_opening (s : Submission) (trap : BitVec (8*s.sizes.trapdoor)) (ps : Positions) :
    s.run .opening (trap,ps)=execute (s.image .opening) (s.steps .opening) (s.initialState .opening (trap,ps)) true := rfl

/-- Every possible output of the official 128-position opening ABI costs at
most 210,404 cycles, for arbitrary trapdoor contents and oracle replies. -/
theorem abi (trap : HonestInputs.Trapdoor) (ps : Positions) (batch : ps.card=BATCH)
    (r : Execution) (hr : r∈support (Artifact.submission.run .opening (trap,ps))) :
    r.cycles≤210404 := by
  have b := HonestRecordExecution.batch trap ps batch 54870 HonestCapComplete.run
  rw [run_opening] at hr
  exact b (Artifact.submission.steps .opening) r hr

/-- The same upper bound holds with probability one in the officially scored
commit-then-open game, including any correlations with the commitment's trapdoor. -/
theorem scored (π : Oracle) (msg : Message) (ps : Positions) (batch : ps.card=BATCH) :
    Pr{let out ← π.run (Artifact.submission.honestMachine msg ps)}[out.1.openingCycles≤210404]=1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr
  have possible := writer_support (π.world.withAddCost Oracle.callCost) _ r hr
  simp only [Submission.honestMachine,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at possible
  obtain ⟨commit,hc,opening,ho,eq⟩ := possible
  rw [eq]
  exact abi _ ps batch opening ho

end CommitGolfCandidate.Reconstruction.HonestOpeningScore
