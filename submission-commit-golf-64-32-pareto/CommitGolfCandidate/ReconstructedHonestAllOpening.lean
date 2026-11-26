import CommitGolfCandidate.ReconstructedHonestAllRecords
import CommitGolfCandidate.ReconstructedHonestWideReceipts
import CommitGolfCandidate.ReconstructedHonestNameReceipts
import CommitGolfCandidate.ReconstructedHonestFuel
import CommitGolfCandidate.ReconstructedEmpty
import CommitGolfCandidate.Machine

namespace CommitGolfCandidate.Reconstruction.HonestAllOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestAllRecords

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode execute

private theorem open_run (s : Submission) (trap : BitVec (8*s.sizes.trapdoor)) (ps : Positions) :
    s.run .opening (trap,ps)=execute (s.image .opening) (s.steps .opening) (s.initialState .opening (trap,ps)) true := rfl

/-- The count-dependent bound includes public permutation charges, cap processing
and the exact return to the ABI on every supported opening input. -/
theorem cycles (trap : HonestInputs.Trapdoor) (ps : Positions) (r : Execution)
    (run : r∈support (Artifact.submission.run .opening (trap,ps))) : r.cycles≤398+ps.card*1212+54870 := by
  by_cases empty : ps=∅
  · subst ps; rw [run_empty_opening,support_pure,Set.mem_singleton_iff] at run; subst r; change 5≤398+0*1212+54870; decide
  · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    rw [open_run] at run
    let fuel := Artifact.submission.steps .opening
    change r∈support (execute HonestWideKernel.image fuel (HonestInputs.initial trap ps) true) at run
    obtain ⟨out,extended,less⟩ := HonestBudget.extend _ _ _ fuel 398 r run
    have start := HonestInputs.first_record trap ps pos fuel
    rw [Nat.add_comm fuel 398,start.1,mem_support_bind_iff] at extended
    obtain ⟨body,remaining,ret⟩ := extended
    rw [support_pure,Set.mem_singleton_iff] at ret
    have resources := budget HonestWideKernel.all_checked HonestNameKernel.all_checked ps.card 0 pos
      (HonestWideMemory.cardinality ps) _ (first trap ps pos) fuel body remaining
    subst out; change r.cycles≤398+body.cycles at less
    omega

/-- The submitted opening image always halts before its allotted fuel, on arbitrary
trapdoor contents and all 0 through 16,777,216-position ABI inputs. -/
theorem halted (trap : HonestInputs.Trapdoor) (ps : Positions) (r : Execution)
    (run : r∈support (Artifact.submission.run .opening (trap,ps))) : r.exit≠.unfinished := by
  have c := cycles trap ps r run
  rw [open_run] at run
  intro unfin
  have used := HonestFuel.charged _ _ _ _ _ run unfin
  change 68719476736≤r.cycles at used
  have size := HonestWideMemory.cardinality ps
  change ps.card≤16777216 at size; omega

theorem termination (π : Oracle) (trap : HonestInputs.Trapdoor) (ps : Positions) :
    Pr{let r ← π.run (Artifact.submission.run .opening (trap,ps))}[r.1.exit≠.unfinished]=1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r h
  exact halted trap ps r.1 (writer_support (π.world.withAddCost Oracle.callCost) _ r h)

end CommitGolfCandidate.Reconstruction.HonestAllOpening
