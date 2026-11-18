import CommitGolfCandidate.MaterializedManifest
import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate
import CommitGolfCandidate.TwoPermutationPinnedBindingCertificate
import CommitGolfCandidate.GroupedCommit

namespace TwoPermutationPrototype.GroupedChecks
open CommitGolf CommitGolf.Riscv OracleComp
abbrev actual := MaterializedArtifact.submission
abbrev prior := PackedChecker.submission
set_option maxRecDepth 16000
set_option maxHeartbeats 700000

private theorem image_eq : actual.image .check=prior.image .check := rfl
private theorem sizes_eq : actual.sizes=prior.sizes := rfl
private theorem layout_eq : actual.layout=prior.layout := rfl
private theorem allowance_eq : actual.steps .check=prior.steps .check := rfl
private theorem same_check (a b : Submission) (layout : a.layout=b.layout) (sizes : a.sizes=b.sizes)
    (image : a.image .check=b.image .check) (steps : a.steps .check=b.steps .check) (i : CheckInput) :
    a.run .check i=b.run .check i := by
  cases a with | mk sz l im st =>
    cases b with | mk sz' l' im' st' =>
      change sz=sz' at sizes
      change l=l' at layout
      subst sz';subst l'
      change im .check=im' .check at image
      change st .check=st' .check at steps
      simp only [Submission.run,Submission.initialState,Submission.inputBuffers,image,steps]

theorem check_run (i : CheckInput) : actual.run .check i=prior.run .check i :=
  same_check actual prior layout_eq sizes_eq image_eq allowance_eq i

private theorem observe_eq (o : Oracle) (i : CheckInput) : Checker.checkObservation actual o i=Checker.checkObservation prior o i := by
  unfold Checker.checkObservation;rw [check_run]

private theorem check_eq : actual.scheme.check=prior.scheme.check := by
  funext root positions values proof
  simp only [Submission.scheme,check_run]

private theorem binding_eq : actual.scheme.Binding ↔ prior.scheme.Binding := by
  simp only [Scheme.Binding,Scheme.Breaks,check_eq]

theorem checker_facts : QuartetCertificate.CheckerFacts actual := by
  have h:=Packed.Checker.executable_checker_facts Sampling.pinned_replay_bound
  constructor
  · intro o i;rw [observe_eq o i];exact h.terminates o i
  · intro o i;rw [observe_eq o i];exact h.queryBudget o i
  · exact binding_eq.mpr h.binding
  · intro o m p salt;rw [observe_eq];exact h.honestAccepted o m p salt

theorem admitted : actual.Admission := by
  intro p;cases p <;> simp only [actual,MaterializedArtifact.submission,Image.Valid,Image.byteSize,LayoutValid,dataBase,
    ArtifactEncoding.length_decode] <;> decide

theorem resources (msg : Message) (z : Execution) (hit : z∈support (actual.run .commit msg)) :
    z.exit=.success ∧ z.cycles=518591774 ∧ z.oracleCalls≤COMMIT_BUDGET := by
  rw [Grouped.commit_of_image actual Grouped.exact_image.symm (by decide) msg ⟨rfl,rfl,rfl,rfl⟩] at hit
  simp only [Grouped.commitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨_,_,_,_,_,_,rfl⟩:=hit
  exact ⟨rfl,rfl,show 43470847≤COMMIT_BUDGET by decide⟩

end TwoPermutationPrototype.GroupedChecks
