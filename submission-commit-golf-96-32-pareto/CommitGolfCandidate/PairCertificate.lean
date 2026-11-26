import CommitGolfCandidate.PairBinding
import CommitGolfCandidate.PairPrivacy
import CommitGolfCandidate.PairResources
import CommitGolfCandidate.Budgets
import CommitGolfCandidate.Completeness

namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure BatchChecks : Prop where
  resources : ∀ (o : Oracle) (input : CheckInput), input.positions.card=BATCH →
    let evaluated := checkEvaluation o (submission.run .check input)
    evaluated.1.exit ≠ .unfinished ∧ evaluated.2 ≤ 2815
  sound : batchSound
  honest : ∀ (o : Oracle) (msg : Message) (s : MachineState), CommittedState o msg s →
    ∀ (ps : Positions), ps.card=BATCH →
    let td := readBuffer s submission.layout.trapdoor submission.sizes.trapdoor
    (o.eval (submission.scheme.check (readBuffer s submission.layout.commitment 32) ps
      (msg.restrict ps) (submission.readProof (openingResult td ps)))).1 = true

private theorem evalRun (o : Oracle) (input : CheckInput) :
    o.run (submission.run .check input) = pure (checkEvaluation o (submission.run .check input)) := by
  by_cases h : input.proof.length ≤ submission.sizes.proof
  · have eqn : submission.run .check input = execute (submission.image .check) (submission.steps .check)
        (submission.initialState .check input) false := by simp only [Submission.run,h,decide_true,if_true]; rfl
    rw [eqn,execute_check_evaluation]
  · have eqn : submission.run .check input = pure ⟨.failure,initialMachine,0,0⟩ := by
      simp [Submission.run,h]
    rw [eqn,oracle_run_pure,check_evaluation_pure]

private theorem termination (ok : BatchChecks) : submission.Termination := by
  intro o p input
  cases p with
  | commit => exact CommitGolfCandidate.submission_termination o .commit input
  | opening => exact opening_termination o input.1 input.2
  | check =>
    by_cases b : input.positions.card=BATCH
    · erw [evalRun o input]
      simp [ok.resources o input b |>.1]
    · rw [check_normal_run input b]
      exact CommitGolfCandidate.check_termination o input

private theorem checkBudget (ok : BatchChecks) (o : Oracle) (input : CheckInput) :
    (o.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).2 ≤
      CHECK_BUDGET input.positions.card := by
  by_cases b : input.positions.card=BATCH
  · rw [scheme_check_evaluation]
    exact (ok.resources o input b).2.trans (by rw [b]; decide)
  · rw [normalCheck input b]
    exact (scheme_check_budget o input).trans (by unfold CHECK_BUDGET; omega)

private theorem budgets (ok : BatchChecks) : submission.scheme.HonestBudgets := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root, trapdoor⟩, commitCalls⟩, committed, rest⟩ := reached
  rw [opening_scheme_execution trapdoor positions, CommitGolfCandidate.oracle_run_pure] at rest
  simp only [support_pure, Set.mem_singleton_iff] at rest
  obtain ⟨opened, rfl, rfl⟩ := rest
  have commitment := scheme_commit_calls oracle message ((root,trapdoor),commitCalls) committed
  refine ⟨?_,Nat.zero_le _, checkBudget ok oracle
    ⟨root,positions,message.restrict positions,submission.readProof (openingResult trapdoor positions)⟩⟩
  change commitCalls ≤ COMMIT_BUDGET
  rw [show commitCalls=5*LENGTH-1 from commitment]; decide

private theorem acceptsHonest (ok : BatchChecks) (o : Oracle) (msg : Message) (s : MachineState)
    (correct : CommittedState o msg s) (ps : Positions) :
    let td := readBuffer s submission.layout.trapdoor submission.sizes.trapdoor
    (o.eval (submission.scheme.check (readBuffer s submission.layout.commitment 32) ps (msg.restrict ps)
      (submission.readProof (openingResult td ps)))).1 = true := by
  by_cases b : ps.card=BATCH
  · exact ok.honest o msg s correct ps b
  · let td := readBuffer s submission.layout.trapdoor submission.sizes.trapdoor
    let root := readBuffer s submission.layout.commitment 32
    have eqn : submission.readProof (openingResult td ps) =
        CommitGolfCandidate.submission.readProof (CommitGolfCandidate.openingResult td ps) :=
      (honestConversion s ps).trans (convert_normal b _)
    change (o.eval (submission.scheme.check root ps (msg.restrict ps) _)).1 = true
    rw [eqn]
    exact ((congrArg (fun c => (o.eval c).1) (normalCheck
      ⟨root,ps,msg.restrict ps,CommitGolfCandidate.submission.readProof (CommitGolfCandidate.openingResult td ps)⟩ b))).trans
      (CommitGolfCandidate.honest_check_accepts o msg s correct ps)

private theorem complete (ok : BatchChecks) : submission.scheme.Completeness := by
  intro o msg ps
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨rt,td⟩,nc⟩,committed,rest⟩ := reached
  rw [opening_scheme_execution td ps,CommitGolfCandidate.oracle_run_pure] at rest
  simp only [support_pure,Set.mem_singleton_iff] at rest
  obtain ⟨opened,rfl,rfl⟩ := rest
  change _ ∈ support (o.run (submission.readCommit <$> submission.run .commit msg)) at committed
  rw [oracle_run_map,support_map] at committed
  obtain ⟨e,reach,eqn⟩ := committed
  have er := congrArg (fun t : (Commitment × submission.scheme.Trapdoor) × Nat => t.1.1) eqn
  have et := congrArg (fun t : (Commitment × submission.scheme.Trapdoor) × Nat => t.1.2) eqn
  change (submission.readCommit e.1).1 = rt at er
  change (submission.readCommit e.1).2 = td at et
  subst rt; subst td
  exact acceptsHonest ok o msg e.1.state (commit_run_matches o msg e reach) ps

theorem certificate_of_batchChecks (checks : BatchChecks) :
    Certificate submission 71680 959447084 40631 where
  admission := admission
  machineSuccess := submission_machine_success
  termination := termination checks
  completeness := complete checks
  honestBudgets := budgets checks
  proofSize := submission_proof_size
  proverCycles := submission_prover_cycles
  binding := pair_submission_binding checks.sound
  hidingProperty := pair_hiding

end CommitGolfCandidate.PairCap
