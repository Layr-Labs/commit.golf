import CommitGolfCandidate.ReconstructedCommitAssembly
import CommitGolfCandidate.ReconstructedCommitEntry
import CommitGolfCandidate.ReconstructedCommitExit

namespace CommitGolfCandidate.Reconstruction.CommitTrace
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitControl CommitSetup CommitSchedule

attribute [local irreducible] ArtifactEncoding.decode execute

private theorem fullTrace : Fragment im 325149296 720507500 56030463
    (fun t => t.pc = 4096 ∧ t.getReg .x20 = 0) (fun _ => False) := by
  have start : Fragment im 8 11 0 (fun t => t.pc = 4096 ∧ t.getReg .x20 = 0) (StateAt 8 0) := by
    intro t ht x hx
    obtain ⟨c,q,next⟩ := boot t ht.1 ht.2 x hx
    exact ⟨c.le,q.le,fun _ => next⟩
  exact compose (compose start CommitAssembly.main_body) CommitExit.finish

private theorem extend (s : MachineState) (init : s.pc = 4096 ∧ s.getReg .x20 = 0) :
    execute im (325149296+748592528) s true = execute im 325149296 s true := by
  apply execute_extra_fuel
  intro r hr
  exact (fullTrace s init r hr).2.2

private theorem abiStart (sub : Submission) (m : Message) :
    (sub.initialState .commit m).pc = 4096 ∧
    (sub.initialState .commit m).getReg .x20 = 0 := ⟨rfl,rfl⟩

private theorem unfold_run (sub : Submission) (m : Message) :
    sub.run .commit m = execute (sub.image .commit) (sub.steps .commit)
      (sub.initialState .commit m) true := rfl

private theorem commitRun (m : Message) :
    Artifact.submission.run .commit m =
      execute im (325149296+748592528) (Artifact.submission.initialState .commit m) true :=
  unfold_run Artifact.submission m

/-- Cost and termination of the actual supplied RV64 commitment, for every possible
private random tape and every sequence of oracle responses. -/
theorem bounded (m : Message) (r : Riscv.Execution)
    (hr : r ∈ support (Artifact.submission.run .commit m)) :
    r.cycles ≤ 720507500 ∧ r.oracleCalls ≤ 56030463 ∧ r.exit ≠ .unfinished := by
  have eqn := (commitRun m).trans (extend _ (abiStart Artifact.submission m))
  have hit := (congrArg (fun g : OracleComp World Execution => r ∈ support g) eqn).mp hr
  exact fullTrace _ (abiStart Artifact.submission m) r hit

end CommitGolfCandidate.Reconstruction.CommitTrace
