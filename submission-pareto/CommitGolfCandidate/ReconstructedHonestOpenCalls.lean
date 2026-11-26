import CommitGolfCandidate.ReconstructedHonestAllOpening
import CommitGolfCandidate.CountingCoins

namespace CommitGolfCandidate.Reconstruction.HonestOpenCalls
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestAllRecords
open HonestWideRecord (Numeric Symbolic)
open HonestWideMemory (capacity)
open HonestWideKernel (image)
open HonestCallFlow (Calls)

set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode execute

theorem records (numeric : Numeric) (symbolic : Symbolic) (n i : Nat) (less : i<n) (bound : n≤capacity)
    (s : MachineState) (ready : Ready n i s) : Calls image s true (n-i) := by
  suffices all : ∀ k i, n-i=k → i<n → ∀ s, Ready n i s → Calls image s true k from all _ i rfl less s ready
  intro k
  induction k with
  | zero => intro i h less; omega
  | succ k ih =>
    intro i h less s ready
    rw [Nat.add_comm k 1]
    apply HonestRecordCost.record_calls k s ready.pc true
    intro t walk
    have step := (iteration numeric symbolic n i less bound s t ready walk).1
    by_cases more : i+1<n
    · rw [ite_eq_left more] at step; exact ih (i+1) (by omega) more t step
    · rw [ite_eq_right more] at step
      have finish := HonestWideCap.calls t step.1 step.2
      exact fun f r hr => (finish f r hr).trans (Nat.zero_le k)

private theorem open_run (s : Submission) (trap : BitVec (8*s.sizes.trapdoor)) (ps : Positions) :
    s.run .opening (trap,ps)=execute (s.image .opening) (s.steps .opening) (s.initialState .opening (trap,ps)) true := rfl

theorem machine (trap : HonestInputs.Trapdoor) (ps : Positions) (r : Execution)
    (run : r∈support (Artifact.submission.run .opening (trap,ps))) : r.oracleCalls≤ps.card := by
  by_cases empty : ps=∅
  · subst ps; rw [run_empty_opening,support_pure,Set.mem_singleton_iff] at run; subst r; exact Nat.zero_le _
  · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    rw [open_run] at run
    let fuel := Artifact.submission.steps .opening
    change r∈support (execute HonestWideKernel.image fuel (HonestInputs.initial trap ps) true) at run
    obtain ⟨out,extended,le⟩ := HonestCallFlow.extend _ _ _ fuel 398 r run
    have start := HonestInputs.first_record trap ps pos fuel
    rw [Nat.add_comm fuel 398,start.1,mem_support_bind_iff] at extended
    obtain ⟨body,remaining,equal⟩ := extended
    rw [support_pure,Set.mem_singleton_iff] at equal
    have cost := records HonestWideKernel.all_checked HonestNameKernel.all_checked ps.card 0 pos
      (HonestWideMemory.cardinality ps) _ (first trap ps pos) fuel body remaining
    subst out; change r.oracleCalls≤0+body.oracleCalls at le
    omega

theorem counted (π : Oracle) (trap : HonestInputs.Trapdoor) (ps : Positions) (r : Execution × Nat)
    (run : r∈support (π.run (Artifact.submission.run .opening (trap,ps)))) : r.2≤ps.card := by
  have h := machine trap ps r.1 (writer_support (π.world.withAddCost Oracle.callCost) _ r run)
  rw [open_run] at run
  rwa [←execute_counted_with_coins π _ _ _ true r run]

theorem opening (π : Oracle) (trap : HonestInputs.Trapdoor) (ps : Positions) (r : Proof × Nat)
    (run : r∈support (π.run (Artifact.submission.scheme.opening trap ps))) : r.2≤OPEN_BUDGET ps.card := by
  change r∈support (π.run (Artifact.submission.readProof <$> Artifact.submission.run .opening (trap,ps))) at run
  rw [oracle_run_map,support_map,Set.mem_image] at run
  obtain ⟨q,inside,rfl⟩ := run
  have h := counted π trap ps q inside
  change q.2≤100*ps.card; omega

end CommitGolfCandidate.Reconstruction.HonestOpenCalls
