import CommitGolfCandidate.ReconstructedHonestRecordFlags
import CommitGolfCandidate.ReconstructedHonestSizeCap
import CommitGolfCandidate.Machine

namespace CommitGolfCandidate.Reconstruction.HonestProofSize
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestFinishes HonestRecordShapes HonestProtected
open HonestRecordMemory (context start)
open HonestRecordIteration (ExitPC ExitShape)
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode execute

theorem records (i : Fin 128) (s : MachineState) (pc0 : s.pc=addr 143) (ready : Holds context (start i.val) s)
    (f : Nat→Bool) (flags : HonestFlagState.Initial f s) (few : HonestSizeSchedule.population f 9 ≤ i.val) :
    SuccessPost HonestCapState.image true HonestSizeExit.Good s := by
  suffices all : ∀ n (i : Fin 128), 128-i.val=n → ∀ s : MachineState, s.pc=addr 143 →
      Holds context (start i.val) s → ∀ f, HonestFlagState.Initial f s → HonestSizeSchedule.population f 9 ≤ i.val →
      SuccessPost HonestCapState.image true HonestSizeExit.Good s from all _ i rfl s pc0 ready f flags few
  intro n
  induction n with
  | zero => intro i h; have := i.isLt; omega
  | succ n ih =>
    intro i h s pc ready f flags few
    refine HonestRecordCost.record_success (good:=HonestSizeExit.Good) s pc true ?_
    intro t path
    obtain ⟨whereAt,state⟩ := HonestRecordIteration.record_step HonestRecordExecution.all_checked i s t true pc ready path
    obtain ⟨event,allowed,effect⟩ := HonestFlagCheck.record_marks HonestFlagCheck.all_checked i s t true pc ready path
    obtain ⟨g,next,bound⟩ := HonestFlagState.transfer f flags event allowed effect
    by_cases more : i.val+1<128
    · simp only [ExitPC,ExitShape,ite_eq_left more] at whereAt state
      exact ih ⟨i.val+1,more⟩ (show 128-(i.val+1)=n by omega) t whereAt state g next
        (show HonestSizeSchedule.population g 9 ≤ i.val+1 by omega)
    · simp only [ExitPC,ExitShape,ite_eq_right more] at whereAt state
      exact HonestSizeCap.run t whereAt state g next (by have := i.isLt; omega)

theorem abi_success (trap : HonestInputs.Trapdoor) (ps : Positions) (batch : ps.card=128) :
    SuccessPost HonestCapState.image true HonestSizeExit.Good (HonestInputs.initial trap ps) := by
  intro fuel r run success
  have longer := HonestSizeExit.extend _ _ _ fuel 398 r run success
  have front := HonestInputs.first_record trap ps (by omega) fuel
  rw [Nat.add_comm fuel 398,front.1,mem_support_bind_iff] at longer
  obtain ⟨v,rest,ret⟩ := longer
  simp only [support_pure,Set.mem_singleton_iff] at ret
  obtain ⟨start,none⟩ := HonestFlagState.init trap ps batch
  have loop := records ⟨0,by decide⟩ _ front.2.1 (HonestRecordMemory.first_shape trap ps batch) _ start (Nat.le_of_eq none)
  subst r
  exact loop fuel v rest success

private theorem opened (s : Submission) (trap : BitVec (8*s.sizes.trapdoor)) (ps : Positions) :
    s.run .opening (trap,ps)=execute (s.image .opening) (s.steps .opening) (s.initialState .opening (trap,ps)) true := rfl

/-- The actual ABI read returns at most 65,544 bytes on every supported 128-position execution. -/
theorem abi (trap : HonestInputs.Trapdoor) (ps : Positions) (batch : ps.card=BATCH) (r : Execution)
    (run : r∈support (Artifact.submission.run .opening (trap,ps))) :
    (Artifact.submission.readProof r).length≤65544 := by
  unfold Submission.readProof
  split
  · rename_i ok
    simp only [Submission.openingSucceeded,Bool.and_eq_true,beq_iff_eq] at ok
    simp only [List.length_map,List.length_range]
    rw [opened] at run
    exact abi_success trap ps batch _ r run ok.1
  · exact Nat.zero_le _

/-- The contest ProofSize proposition for the manifest executable. -/
theorem scored : Artifact.submission.scheme.ProofSize 65544 := by
  intro π message ps batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reached
  simp only [Scheme.honest,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨commit,_,opening,opened,out⟩ := reached
  rw [out]
  have inside := writer_support (π.world.withAddCost Oracle.callCost) _ opening opened
  change opening.1∈support (Artifact.submission.readProof <$> Artifact.submission.run .opening (commit.1.2,ps)) at inside
  simp only [support_map,Set.mem_image] at inside
  obtain ⟨exec,hr,e⟩ := inside
  change opening.1.length≤65544
  rw [←e]; exact abi commit.1.2 ps batch exec hr

end CommitGolfCandidate.Reconstruction.HonestProofSize
