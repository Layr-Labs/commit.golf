import CommitGolfCandidate.TruncCommitResources
import CommitGolfCandidate.TruncChecks
import CommitGolfCandidate.TruncPrivacy
import CommitGolfCandidate.TruncBinding
import CommitGolfCandidate.TruncWireStages
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 11000
set_option maxHeartbeats 210000
private theorem evalRun (o : Oracle) (input : CheckInput) :
    o.run (submission.run .check input) = pure (checkEvaluation o (submission.run .check input)) := by
  by_cases h : input.proof.length ≤ submission.sizes.proof
  · have eqn : submission.run .check input = execute (submission.image .check) (submission.steps .check)
        (submission.initialState .check input) false := by simp only [Submission.run,h,decide_true,if_true]; rfl
    rw [eqn,execute_check_evaluation]
  · have eqn : submission.run .check input = pure ⟨.failure,initialMachine,0,0⟩ := by
      simp [Submission.run,h]
    rw [eqn,oracle_run_pure,check_evaluation_pure]


private theorem termination (law : Wire.PackRun) : submission.Termination := by
  intro o prog input;cases prog with
  | commit =>
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro z hit
    have r:=commit_input_resources input z.1 (writer_support (o.world.withAddCost Oracle.callCost) _ z hit)
    rw [r.1];decide
  | opening=>exact Open.opening_termination law o input.1 input.2
  | check=>erw [evalRun o input];simp [(checkResources o input).1]

private theorem checkBudget (o : Oracle) (i : CheckInput) :
    (o.eval (submission.scheme.check i.commitment i.positions i.values i.proof)).2≤CHECK_BUDGET i.positions.card := by
  rw [scheme_check_evaluation];exact (checkResources o i).2
private theorem budgets (law : Wire.PackRun) : submission.scheme.HonestBudgets := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root, trapdoor⟩, commitCalls⟩, committed, rest⟩ := reached
  rw [Open.opening_scheme_execution law trapdoor positions, CommitGolfCandidate.oracle_run_pure] at rest
  simp only [support_pure, Set.mem_singleton_iff] at rest
  obtain ⟨opened, rfl, rfl⟩ := rest
  have commitment := scheme_commit_calls oracle message ((root,trapdoor),commitCalls) committed
  refine ⟨?_,Nat.zero_le _, checkBudget oracle
    ⟨root,positions,message.restrict positions,submission.readProof (Open.openingResult trapdoor positions)⟩⟩
  change commitCalls ≤ COMMIT_BUDGET
  rw [show commitCalls=5*LENGTH-1 from commitment]; decide

private theorem complete (law : Wire.PackRun) (bytes : Wire.PackedBytes) : submission.scheme.Completeness := by
  intro o msg ps
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨rt,td⟩,nc⟩,committed,rest⟩ := reached
  rw [Open.opening_scheme_execution law td ps,CommitGolfCandidate.oracle_run_pure] at rest
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
  exact acceptsHonest bytes o msg e.1.state (committedOrigin o msg e reach) ps


theorem certificate : Certificate submission 68096 963641394 109773 where
  admission := admission
  machineSuccess := submission_machine_success Wire.packRun
  termination := termination Wire.packRun
  completeness := complete Wire.packRun Wire.packedBytes
  honestBudgets := budgets Wire.packRun
  proofSize := Open.submission_proof_size Wire.packRun
  proverCycles := submission_prover_cycles Wire.packRun
  binding := trunc_submission_binding checkedSound
  hidingProperty := truncHiding Wire.packRun Wire.packedBytes
end CommitGolfCandidate.Trunc
