import CommitGolfCandidate.S4Resources
import CommitGolfCandidate.S4Honest
namespace CommitGolfCandidate.S4
open CommitGolf CommitGolf.Riscv OracleComp
open Late (words wordTape endCommit trapdoorOf cachedLevels)
set_option maxRecDepth 8000
attribute [local irreducible] List.range List.finRange Late.words S4Hiding.tree Late.trapdoorOf Late.cachedLevels opening
private def checked (o : Oracle) (i : CheckInput) :=
  o.eval (Late.submission.scheme.check i.commitment i.positions i.values i.proof)

private theorem honestRun (op : OpeningLaw) (o : Oracle) (m : Message) (ps : Positions) :
    Late.submission.scheme.honest o m ps=
      (do let ws←words
          let i:=canonicalInput m ps (cachedLevels o m ws) (wordTape ws)
          let c:=checked o i
          pure ⟨c.1,78293686,0,c.2,i.proof.length⟩) := by
  unfold Scheme.honest
  rw [Late.commit_scheme_run,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro ws mem
  simp only [pure_bind,openScheme op]
  rw [proofOfTape op o m ws mem ps]
  rfl

private theorem machineRun (op : OpeningLaw) (o : Oracle) (m : Message) (ps : Positions) :
    o.run (Late.submission.honestMachine m ps)=
      (do let ws←words
          let e:=op.result (trapdoorOf o m ws) ps
          pure (⟨true,863218785,e.cycles,(Late.submission.readProof e).length⟩,78293686)) := by
  unfold Submission.honestMachine
  rw [oracle_run_bind,Late.full_commit_run,bind_assoc]
  apply bind_congr;intro ws
  simp only [pure_bind,op.run,oracle_run_pure,Nat.add_zero,op.success,Bool.and_true]
  unfold trapdoorOf;rfl

private theorem termination (op : OpeningLaw) (ch : CheckLaw) : Late.submission.Termination := by
  intro o prog input
  cases prog with
  | commit=>exact Late.commit_terminates o input
  | opening=>
    rcases input with ⟨td,ps⟩
    rw [op.run,oracle_run_pure]
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr;intro result reach
    rw [support_pure,Set.mem_singleton_iff] at reach;subst result
    rw [op.exit];decide
  | check=>
    have deterministic : o.run (Late.submission.run .check input)=pure (Machine.checkEvaluation o (Late.submission.run .check input)) := by
      by_cases fit : input.proof.length≤Late.submission.sizes.proof
      · simp only [Submission.run,fit,decide_true,ite_true];exact Machine.execute_check_evaluation ..
      · simp only [Submission.run,fit,decide_false,Bool.false_eq_true,ite_false,oracle_run_pure,Machine.check_evaluation_pure]
    rw [deterministic];apply (OracleComp.prEvent_eq_one_iff _ _).mpr;intro r reach
    rw [support_pure,Set.mem_singleton_iff] at reach;subst r;exact ch.terminates o input

theorem fromMachine (op : OpeningLaw) (ch : CheckLaw) : Certificate Late.submission 70410 863218785 85548 where
  admission:=Late.admission
  termination:=termination op ch
  machineSuccess:=by
    intro o m ps;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro r hr;rw [machineRun op,mem_support_bind_iff] at hr
    obtain ⟨_,_,h⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at h;subst r;rfl
  proverCycles:=by
    intro o m ps b;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro r hr;rw [machineRun op,mem_support_bind_iff] at hr
    obtain ⟨ws,_,h⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at h;subst r
    exact ⟨le_rfl,op.priced _ _ b⟩
  completeness:=by
    intro o m ps;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro r hr;rw [honestRun op,mem_support_bind_iff] at hr
    obtain ⟨ws,_,h⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at h;subst r
    exact (ch.valid o _).mpr (honestValid o.compression m ps _ _ (by unfold cachedLevels;exact honestTree _ _ _))
  honestBudgets:=by
    intro o m ps;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro r hr;rw [honestRun op,mem_support_bind_iff] at hr
    obtain ⟨ws,_,h⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at h;subst r
    exact ⟨by exact (by decide : 78293686≤COMMIT_BUDGET),Nat.zero_le _,ch.calls o (canonicalInput m ps (cachedLevels o m ws) (wordTape ws))⟩
  proofSize:=by
    intro o m ps b;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro r hr;rw [honestRun op,mem_support_bind_iff] at hr
    obtain ⟨ws,_,h⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at h;subst r
    change (opening .byte _ _ ps).length≤70410;rw [openingSize,if_pos b];rfl
  binding:=trunc_submission_binding (fun o i=>(ch.valid o i).mp)
  hidingProperty:=machineHiding op
end CommitGolfCandidate.S4
