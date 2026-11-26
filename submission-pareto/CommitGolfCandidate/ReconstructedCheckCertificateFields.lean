import CommitGolfCandidate.ReconstructedOpeningDelivery
import CommitGolfCandidate.ReconstructedHonestOpenCalls
import CommitGolfCandidate.ReconstructedBindingGame

namespace CommitGolfCandidate.Reconstruction.CheckCertificateFields
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling TwoPermutationPrototype.Checker
set_option maxRecDepth 15000
attribute [local irreducible] ArtifactEncoding.decode execute

noncomputable def HonestInput (o : Oracle) (k : Generator.Key) (msg : Message) (ps : Positions) : CheckInput :=
  ⟨Binding.pack (LeafTree.tree o k msg 0 1),ps,msg.restrict ps,
    Wire.bytes (Encoding.fields (LeafTree.tree o k msg) ps (HonestDelivery.salts o k ps))⟩

def HonestChecker := ∀ (o : Oracle) (k : Generator.Key) (msg : Message) (ps : Positions),
  let obs := checkObservation Artifact.submission o (HonestInput o k msg ps)
  obs.1.1.exit=.success ∧ obs.2≤CHECK_BUDGET ps.card

def TotalChecker := ∀ (o : Oracle) (input : CheckInput),
  (checkObservation Artifact.submission o input).1.1.exit≠.unfinished

theorem termination (total : TotalChecker) : Artifact.submission.Termination := by
  intro o p input
  cases p with
  | commit =>
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro r hr
    obtain ⟨⟨k,completed⟩,_,_⟩ := CommitMachine.counted_output o input r hr
    rw [completed.success];decide
  | opening => exact HonestAllOpening.termination o input.1 input.2
  | check =>
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro r hr
    have mem : r.1∈support (fixedOracleRun o (Artifact.submission.run .check input)) := by
      rw [fixedOracleRun,support_map];exact ⟨r,hr,rfl⟩
    rw [(check_public_only Artifact.submission input).fixed o,support_pure,Set.mem_singleton_iff] at mem
    have er := check_record_erase o (Artifact.submission.run .check input)
    change ((checkObservation Artifact.submission o input).1.1,(checkObservation Artifact.submission o input).2)=_ at er
    rw [mem,←er];exact total o input

private theorem viewed (o : Oracle) (k : Generator.Key) (msg : Message) (ps : Positions) :
    (OpeningView.view o k msg ps).2=(HonestInput o k msg ps).proof := by
  unfold HonestInput
  rw [LeafProjection.reference_tree];rfl

theorem honest (checker : HonestChecker) (o : Oracle) (msg : Message) (ps : Positions)
    (r : Scheme.HonestResult) (hr : r∈support (Artifact.submission.scheme.honest o msg ps)) :
    r.accepted=true ∧ r.commitCalls≤COMMIT_BUDGET ∧ r.openCalls≤OPEN_BUDGET ps.card ∧ r.checkCalls≤CHECK_BUDGET ps.card := by
  simp only [Scheme.honest,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hr
  obtain ⟨commit,hc,pf,hp,out⟩ := hr
  have openCost := HonestOpenCalls.opening o commit.1.2 ps pf hp
  change commit∈support (o.run (Artifact.submission.readCommit <$> Artifact.submission.run .commit msg)) at hc
  rw [oracle_run_map,support_map] at hc
  obtain ⟨exec,ran,eq⟩ := hc
  obtain ⟨⟨k,completed⟩,_,cost⟩ := CommitMachine.counted_output o msg exec ran
  have fromRoot : commit.1.1=(HonestInput o k msg ps).commitment := by
    rw [←eq];exact completed.output
  have stored : CommitStorage.Stored o k msg commit.1.2 := by rw [←eq];exact completed.contents
  have op : pf.1∈support (fixedOracleRun o (Artifact.submission.scheme.opening commit.1.2 ps)) := by
    rw [fixedOracleRun,support_map];exact ⟨pf,hp,rfl⟩
  rw [HonestDelivery.emits OpeningDelivery.lower o k msg _ ps stored,support_pure,Set.mem_singleton_iff] at op
  have proof := op.trans (viewed o k msg ps)
  let input := HonestInput o k msg ps
  have ev := scheme_check_evaluation o Artifact.submission input
  have er := check_record_erase o (Artifact.submission.run .check input)
  change ((checkObservation Artifact.submission o input).1.1,(checkObservation Artifact.submission o input).2)=_ at er
  rw [←er] at ev
  have ok := checker o k msg ps
  rw [out]
  change (o.eval (Artifact.submission.scheme.check commit.1.1 ps (msg.restrict ps) pf.1)).1=true ∧
    commit.2≤COMMIT_BUDGET ∧ pf.2≤OPEN_BUDGET ps.card ∧ (o.eval (Artifact.submission.scheme.check commit.1.1 ps (msg.restrict ps) pf.1)).2≤CHECK_BUDGET ps.card
  rw [fromRoot,proof]
  change (o.eval (Artifact.submission.scheme.check input.commitment input.positions input.values input.proof)).1=true ∧
    commit.2≤COMMIT_BUDGET ∧ pf.2≤OPEN_BUDGET ps.card ∧ (o.eval (Artifact.submission.scheme.check input.commitment input.positions input.values input.proof)).2≤CHECK_BUDGET ps.card
  rw [ev]
  refine ⟨beq_iff_eq.mpr ok.1,?_,openCost,ok.2⟩
  rw [←eq];exact cost.trans (by decide)

theorem completeness (h : HonestChecker) : Artifact.submission.scheme.Completeness := by
  intro o msg ps
  exact (OracleComp.prEvent_eq_one_iff _ _).mpr (fun r hr => (honest h o msg ps r hr).1)

theorem budgets (h : HonestChecker) : Artifact.submission.scheme.HonestBudgets := by
  intro o msg ps
  exact (OracleComp.prEvent_eq_one_iff _ _).mpr (fun r hr => (honest h o msg ps r hr).2)

end CommitGolfCandidate.Reconstruction.CheckCertificateFields
