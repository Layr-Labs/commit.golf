import CommitGolfCandidate.ReconstructedCheckCertificateFields
import CommitGolfCandidate.ReconstructedCheckEmptyTrace

namespace CommitGolfCandidate.Reconstruction.CheckHonestEmpty
open CommitGolf CommitGolf.Riscv CheckCertificateFields OracleComp
open TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
set_option maxRecDepth 14000
attribute [local irreducible] execute ArtifactEncoding.decode

theorem run (o : Oracle) (key : Generator.Key) (msg : Message) :
    let obs:=checkObservation Artifact.submission o (HonestInput o key msg ∅)
    obs.1.1.exit=.success ∧ obs.2=0 := by
  let root:=Binding.pack (LeafTree.tree o key msg 0 1)
  let val:=msg.restrict ∅
  let input : CheckInput:=⟨root,∅,val,[]⟩
  have none : (HonestInput o key msg ∅).proof=[]:=by
    apply List.length_eq_zero_iff.mp
    change (Wire.bytes (Encoding.fields _ ∅ _)).length=0
    rw [Wire.byte_count,Encoding.all_bits,Finset.sort_empty]
    decide +kernel
  have eq : HonestInput o key msg ∅=input:=by
    change (⟨root,∅,val,(HonestInput o key msg ∅).proof⟩ : CheckInput)=⟨root,∅,val,[]⟩
    rw [none]
  change (checkObservation Artifact.submission o _).1.1.exit=.success ∧ (checkObservation Artifact.submission o _).2=0
  rw [eq]
  unfold checkObservation
  rw [show Artifact.submission.run .check input=_ from run_empty_check root val,record_rows_pure,check_evaluation_pure]
  exact ⟨rfl,rfl⟩

end CommitGolfCandidate.Reconstruction.CheckHonestEmpty

