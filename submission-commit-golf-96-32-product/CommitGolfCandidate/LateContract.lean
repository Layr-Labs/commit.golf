import CommitGolfCandidate.LateCheckFinish
import CommitGolfCandidate.LateHonestModel
import CommitGolfCandidate.LateCertificate

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv OracleComp
set_option maxRecDepth 6000
attribute [local irreducible] words Check.evaluation honestInput

theorem completeness_of_law (law : Check.MachineLaw) : submission.scheme.Completeness := by
  intro o m p
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reach
  rw [honest_distribution,mem_support_bind_iff] at reach
  obtain ⟨ws,_,e⟩:=reach
  rw [support_pure,Set.mem_singleton_iff] at e;subst r
  exact (law o _).2.mpr (Check.honest_valid o m ws p)

theorem honest_budgets_of_law (law : Check.MachineLaw) : submission.scheme.HonestBudgets := by
  intro o m p
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reach
  rw [honest_distribution,mem_support_bind_iff] at reach
  obtain ⟨ws,_,e⟩:=reach
  rw [support_pure,Set.mem_singleton_iff] at e;subst r
  refine ⟨(by decide : 83886079≤COMMIT_BUDGET),Nat.zero_le _,?_⟩
  have q:=(law o (honestInput o m ws p)).1
  have positions : (honestInput o m ws p).positions=p := by unfold honestInput;rfl
  rw [positions] at q
  change (Check.evaluation o (honestInput o m ws p)).2≤100*p.card
  split at q
  · rename_i b;change p.card=128 at b;omega
  · omega

theorem certificate_of_checker_runs (batch : Check.BatchEvaluation) (normal : Check.NormalEvaluation)
    (late_hiding : HidingGoal) : Certificate submission 72704 911802772 45875 := by
  let law:=Check.law_of_evaluations batch normal
  exact certificate_of_refinements machine_success (Check.termination_of_evaluations batch normal)
    (completeness_of_law law) (honest_budgets_of_law law) proof_size prover_cycles (Check.sound_of_machine law)
    view_refinement late_hiding

end CommitGolfCandidate.Late
