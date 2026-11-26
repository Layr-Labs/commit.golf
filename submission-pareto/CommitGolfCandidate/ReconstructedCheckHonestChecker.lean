import CommitGolfCandidate.ReconstructedCheckHonestPositive
import CommitGolfCandidate.ReconstructedCheckHonestEmpty
import CommitGolfCandidate.ReconstructedCheckHonestAdmission

namespace CommitGolfCandidate.Reconstruction.CheckHonestChecker
open CommitGolf CommitGolf.Riscv CheckCertificateFields
open TwoPermutationPrototype.Checker

/-- The concrete checker accepts every opening emitted by the concrete opener and stays within
the public-query budget at every cardinality. -/
theorem verified : HonestChecker := by
  intro o key msg ps
  by_cases pos : ps.Nonempty
  · let input:=HonestInput o key msg ps
    have g:=CheckHonestAdmission.wire ps (LeafTree.tree o key msg) (HonestDelivery.salts o key ps)
    exact CheckHonestPositive.run o key msg input pos g.1 g.2 rfl (fun _=>rfl) rfl
  · have eq : ps=∅:=Finset.not_nonempty_iff_eq_empty.mp pos
    subst ps
    obtain ⟨ok,q⟩:=CheckHonestEmpty.run o key msg
    exact ⟨ok,q.le.trans (Nat.zero_le _)⟩

end CommitGolfCandidate.Reconstruction.CheckHonestChecker

