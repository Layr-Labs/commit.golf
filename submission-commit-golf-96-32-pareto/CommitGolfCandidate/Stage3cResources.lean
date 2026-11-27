import CommitGolfCandidate.Stage3cOpeningLaw
import CommitGolfCandidate.Stage3cHonestWire
import CommitGolfCandidate.Stage3cCheckEvaluation
import CommitGolfCandidate.Stage3cAdmission
import CommitGolfCandidate.Stage3cBinding
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv OracleComp
open Late (PairCoins)
attribute [local irreducible] endCommit List.range Chained.Binary.opening cachedLevels trapdoorOf Chained.Binary.treeM Late.node
noncomputable abbrev canonicalInput := Pw.canonicalInput
def checked (o : Oracle) (i : CheckInput) := o.eval (Artifact.submission.scheme.check i.commitment i.positions i.values i.proof)
theorem commit_terminates (o : Oracle) (m : Message) :
    Pr{let r ←o.run (Artifact.submission.run .commit m)}[r.1.exit≠Exit.unfinished]=1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr;rw [full_commit_run,mem_support_bind_iff] at hr
  obtain ⟨ws,_,in_⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at in_;subst r;unfold endCommit;exact (by decide : Exit.success≠Exit.unfinished)

theorem machine_run (o : Oracle) (m : Message) (ps : Positions) :
    o.run (Artifact.submission.honestMachine m ps)=
      (do let ws←coinTape;let e:=opened (trapdoorOf o m ws) ps
          pure (⟨true,911200264,e.cycles,(Artifact.submission.readProof e).length⟩,84087039)) := by
  unfold Submission.honestMachine
  rw [oracle_run_bind,full_commit_run,bind_assoc]
  apply bind_congr;intro ws
  simp only [pure_bind,(open_law ..).run,oracle_run_pure,Nat.add_zero,(open_law ..).success,Bool.and_true]
  unfold trapdoorOf endCommit;rfl

theorem machine_success : Artifact.submission.MachineSuccess := by
  intro o m ps;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr;rw [machine_run,mem_support_bind_iff] at hr
  obtain ⟨_,_,in_⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at in_;subst r;rfl

theorem prover_cycles : Artifact.submission.ProverCycles 911200264 186934 := by
  intro o m ps b;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr;rw [machine_run,mem_support_bind_iff] at hr
  obtain ⟨ws,_,in_⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at in_;subst r
  exact ⟨le_rfl,(open_law _ ps).price b⟩

theorem honest_run (o : Oracle) (m : Message) (ps : Positions) :
    Artifact.submission.scheme.honest o m ps=
      (do let ws←coinTape;let i:=canonicalInput o m ps (wordTape ws);let c:=checked o i
          pure ⟨c.1,84087039,0,c.2,i.proof.length⟩) := by
  unfold Scheme.honest
  rw [commit_scheme_run,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro ws mem
  simp only [pure_bind,open_scheme]
  rw [proof_of_tape o m ws mem ps];unfold cachedLevels;rfl

theorem proof_size : Artifact.submission.scheme.ProofSize 67840 := by
  intro o m ps batch;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr;rw [honest_run,mem_support_bind_iff] at hr
  obtain ⟨ws,_,in_⟩:=hr;rw [support_pure,Set.mem_singleton_iff] at in_;subst r
  change (Chained.Binary.opening _ _ ps).length≤67840
  simp only [Chained.Binary.opening,if_pos batch,Chained.Binary.packed,List.length_map,List.length_range]
  rw [Chained.Binary.field_geometry.2]

structure CheckerLaw where
  replay : Pw.CheckReplay Artifact.submission.scheme
  terminates : ∀ o (i : CheckInput),(Check.checkEvaluation o (Artifact.submission.run .check i)).1.exit≠.unfinished
  honest : ∀ o m ps salt,let i:=canonicalInput o m ps salt
           (checked o i).1=true ∧ (checked o i).2≤CHECK_BUDGET ps.card

theorem from_checker (ch : CheckerLaw) : Certificate Artifact.submission 67840 911200264 186934 where
  admission:=admission
  machineSuccess:=machine_success
  proverCycles:=prover_cycles
  proofSize:=proof_size
  hidingProperty:=machine_hiding
  binding:=Pw.check_binding ch.replay
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
    exact ⟨(by decide : 84087039≤COMMIT_BUDGET),Nat.zero_le _,(ch.honest o m ps (wordTape ws)).2⟩
end CommitGolfCandidate.Chained.BinaryMachine
