import CommitGolfCandidate.S5OpeningLaw
import CommitGolfCandidate.S5CheckEvaluation
import CommitGolfCandidate.S5Admission
import CommitGolfCandidate.S5Binding
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv OracleComp
open Late (PairCoins)
attribute [local irreducible] endCommit S5Hiding.tree List.range S5.opening cachedLevels trapdoorOf
noncomputable def canonicalInput (o : Oracle) (m : Message) (ps : Positions) (salt : Late.SaltTape) : CheckInput :=
  let tree:=S5Hiding.tree o.compression m salt
  ⟨Late.node tree LOG_LENGTH 0,ps,m.restrict ps,S5.opening tree salt ps⟩
def checked (o : Oracle) (i : CheckInput) := o.eval (Artifact.submission.scheme.check i.commitment i.positions i.values i.proof)
theorem commit_terminates (o : Oracle) (m : Message) :
    Pr{let r ←o.run (Artifact.submission.run .commit m)}[r.1.exit≠Exit.unfinished]=1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr;rw [full_commit_run,mem_support_bind_iff] at hr
  obtain ⟨ws,_,in_⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at in_;subst r;unfold endCommit;exact (by decide : Exit.success≠Exit.unfinished)

theorem machine_run (o : Oracle) (m : Message) (ps : Positions) :
    o.run (Artifact.submission.honestMachine m ps)=
      (do let ws←coinTape;let e:=opened (trapdoorOf o m ws) ps
          pure (⟨true,860276380,e.cycles,(Artifact.submission.readProof e).length⟩,78427694)) := by
  unfold Submission.honestMachine
  rw [oracle_run_bind,full_commit_run,bind_assoc]
  apply bind_congr;intro ws
  simp only [pure_bind,(open_law ..).run,oracle_run_pure,Nat.add_zero,(open_law ..).success,Bool.and_true]
  unfold trapdoorOf endCommit;rfl

theorem machine_success : Artifact.submission.MachineSuccess := by
  intro o m ps;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr;rw [machine_run,mem_support_bind_iff] at hr
  obtain ⟨_,_,in_⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at in_;subst r;rfl

theorem prover_cycles : Artifact.submission.ProverCycles 860276380 191023 := by
  intro o m ps b;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr;rw [machine_run,mem_support_bind_iff] at hr
  obtain ⟨ws,_,in_⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at in_;subst r
  exact ⟨le_rfl,(open_law _ ps).price b⟩

theorem honest_run (o : Oracle) (m : Message) (ps : Positions) :
    Artifact.submission.scheme.honest o m ps=
      (do let ws←coinTape;let i:=canonicalInput o m ps (wordTape ws);let c:=checked o i
          pure ⟨c.1,78427694,0,c.2,i.proof.length⟩) := by
  unfold Scheme.honest
  rw [commit_scheme_run,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro ws mem
  simp only [pure_bind,open_scheme]
  rw [proof_of_tape o m ws mem ps];unfold cachedLevels;rfl

theorem proof_size : Artifact.submission.scheme.ProofSize 69396 := by
  intro o m ps batch;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr;rw [honest_run,mem_support_bind_iff] at hr
  obtain ⟨ws,_,in_⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at in_;subst r
  change (S5.opening _ _ ps).length≤69396
  simp only [S5.opening,if_pos batch,List.length_map,List.length_range];rfl

structure CheckerLaw where
  replay : S5.CheckReplay Artifact.submission.scheme
  terminates : ∀ o (i : CheckInput),(Check.checkEvaluation o (Artifact.submission.run .check i)).1.exit≠.unfinished
  honest : ∀ o m ps salt,let i:=canonicalInput o m ps salt
           (checked o i).1=true ∧ (checked o i).2≤CHECK_BUDGET ps.card

theorem from_checker (ch : CheckerLaw) : Certificate Artifact.submission 69396 860276380 191023 where
  admission:=admission
  machineSuccess:=machine_success
  proverCycles:=prover_cycles
  proofSize:=proof_size
  hidingProperty:=machine_hiding
  binding:=S5.check_binding ch.replay
  termination:=by
    intro o p input
    cases p with
    | commit=>exact commit_terminates o input
    | opening=>
      obtain ⟨td,ps⟩:=input
      rw [(open_law td ps).run,oracle_run_pure]
      apply (OracleComp.prEvent_eq_one_iff _ _).mpr;intro r hr
      rw [support_pure,Set.mem_singleton_iff] at hr;subst r;rw [(open_law td ps).exit];decide
    | check=>
      have deterministic : o.run (Artifact.submission.run .check input)=pure (Check.checkEvaluation o (Artifact.submission.run .check input)) := by
        by_cases fit : input.proof.length≤Artifact.submission.sizes.proof
        · simp only [Submission.run,fit,decide_true,ite_true];exact Check.execute_check_evaluation ..
        · simp only [Submission.run,fit,decide_false,Bool.false_eq_true,ite_false,oracle_run_pure,Check.check_evaluation_pure]
      rw [deterministic];apply (OracleComp.prEvent_eq_one_iff _ _).mpr;intro r hr
      rw [support_pure,Set.mem_singleton_iff] at hr;subst r;exact ch.terminates o input
  completeness:=by
    intro o m ps;apply (OracleComp.prEvent_eq_one_iff _ _).mpr;intro r hr
    rw [honest_run,mem_support_bind_iff] at hr;obtain ⟨ws,_,in_⟩:=hr
    rw [support_pure,Set.mem_singleton_iff] at in_;subst r;exact (ch.honest o m ps (wordTape ws)).1
  honestBudgets:=by
    intro o m ps;apply (OracleComp.prEvent_eq_one_iff _ _).mpr;intro r hr
    rw [honest_run,mem_support_bind_iff] at hr;obtain ⟨ws,_,in_⟩:=hr
    rw [support_pure,Set.mem_singleton_iff] at in_;subst r
    exact ⟨(by decide : 78427694≤COMMIT_BUDGET),Nat.zero_le _,(ch.honest o m ps (wordTape ws)).2⟩
end CommitGolfCandidate.S5Machine
