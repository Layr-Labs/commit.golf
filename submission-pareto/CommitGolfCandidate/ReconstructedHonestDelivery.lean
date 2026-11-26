import CommitGolfCandidate.ReconstructedCapComplete
import CommitGolfCandidate.ReconstructedExecutableHiding
import CommitGolfCandidate.ReconstructedHonestAllOpening

namespace CommitGolfCandidate.Reconstruction.HonestDelivery
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open HonestCapState (image)
open CommitBlocks (addr)
set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode execute
local instance discrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def salts (o : Oracle) (key : Generator.Key) (ps : Positions) : OpenedSalts ps :=
  fun i => HidingTape.actualTape o.permutation key i.val

/-- The lower-record executor is measured only until the first cap instruction.
The ABI loader and every later step are supplied by the independently checked phases. -/
def Lower (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions) :=
  ∃ n t, n≤2000*ps.card ∧ CommitExact.Segment o image n (HonestInputs.first trap ps) t ∧
    CapEntry.Ready t trap ps (CapIterate.records (LeafTree.tree o key msg) ps (salts o key ps))

def LowerAll := ∀ (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions),
  0<ps.card → CommitStorage.Stored o key msg trap → Lower o key msg trap ps

def Done (o : Oracle) (key : Generator.Key) (msg : Message) (ps : Positions) (e : Execution) : Prop :=
  Artifact.submission.openingSucceeded e=true ∧ Artifact.submission.readProof e=(OpeningView.view o key msg ps).2

private theorem open_run (s : Submission) (trap : BitVec (8*s.sizes.trapdoor)) (ps : Positions) :
    s.run .opening (trap,ps)=execute (s.image .opening) (s.steps .opening) (s.initialState .opening (trap,ps)) true := rfl

private theorem view (o : Oracle) (key : Generator.Key) (msg : Message) (ps : Positions) :
    Wire.bytes (Encoding.fields (LeafTree.tree o key msg) ps (salts o key ps))=(OpeningView.view o key msg ps).2 := by
  rw [LeafProjection.reference_tree];rfl

theorem positive (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (pos : 0<ps.card) (stored : CommitStorage.Stored o key msg trap) (lower : Lower o key msg trap ps) :
    ∃ e : Execution, fixedOracleRun o (Artifact.submission.run .opening (trap,ps))=pure e ∧ Done o key msg ps e := by
  obtain ⟨n,u,lim,records,ready⟩ := lower
  have entry : CommitExact.Segment o image 398 (HonestInputs.initial trap ps) (HonestInputs.first trap ps) :=
    ⟨398,0,fun fuel => by rw [(HonestInputs.first_record trap ps pos fuel).1,bind_pure_comp,fixed_oracle_run_map]⟩
  obtain ⟨m,t,c,q,cap,finish,bytes⟩ := CapComplete.run o key msg trap ps stored pos (salts o key ps) u ready
  obtain ⟨before,queries,stem⟩ := CommitExact.compose entry records
  let e : Execution := ⟨.success,t,before+c,queries+q⟩
  refine ⟨e,?_,(bytes _ _).1,((bytes _ _).2).trans (view o key msg ps)⟩
  rw [open_run]
  let fuel := Artifact.submission.steps .opening
  have count := HonestWideMemory.cardinality ps
  change ps.card≤16777216 at count
  have small : 398+n+m≤fuel := by change 398+n+m≤68719476736;omega
  change fixedOracleRun o (execute image fuel (HonestInputs.initial trap ps) true)=_
  rw [show fuel=(398+n)+(m+(fuel-(398+n+m))) by omega,stem,finish,map_pure]
  rfl

theorem actual (lower : LowerAll) (o : Oracle) (key : Generator.Key) (msg : Message)
    (trap : CommitStorage.Trapdoor) (ps : Positions) (stored : CommitStorage.Stored o key msg trap) :
    ∃ e : Execution, fixedOracleRun o (Artifact.submission.run .opening (trap,ps))=pure e ∧ Done o key msg ps e := by
  by_cases pos : 0<ps.card
  · exact positive o key msg trap ps pos stored (lower o key msg trap ps pos stored)
  · have h : ps=∅ := Finset.card_eq_zero.mp (by omega)
    subst ps
    let t := emptyFinal (Artifact.submission.initialState .opening (trap,∅))
    refine ⟨⟨.success,t,5,0⟩,?_,?_,?_⟩
    · rw [run_empty_opening,fixed_oracle_run_pure]
    · rfl
    · rw [OpeningView.empty_view]
      change Artifact.submission.readProof ⟨.success,t,5,0⟩=[]
      simp only [Submission.readProof,show Artifact.submission.openingSucceeded ⟨.success,t,5,0⟩=true from rfl,ite_true]
      rfl

theorem emits (lower : LowerAll) (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor)
    (ps : Positions) (stored : CommitStorage.Stored o key msg trap) :
    fixedOracleRun o (Artifact.submission.scheme.opening trap ps)=pure (OpeningView.view o key msg ps).2 := by
  obtain ⟨e,run,h⟩ := actual lower o key msg trap ps stored
  change fixedOracleRun o (Artifact.submission.readProof <$> Artifact.submission.run .opening (trap,ps))=_
  rw [fixed_oracle_run_map,run,map_pure,h.2]

theorem machine (lower : LowerAll) : Artifact.submission.MachineSuccess := by
  intro o msg ps
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r member
  have possible : r.1∈support (fixedOracleRun o (Artifact.submission.honestMachine msg ps)) := by
    rw [fixedOracleRun,support_map,Set.mem_image];exact ⟨r,member,rfl⟩
  simp only [Submission.honestMachine,fixed_oracle_run_bind,fixed_oracle_run_pure,mem_support_bind_iff,
    support_pure,Set.mem_singleton_iff] at possible
  obtain ⟨committed,commitRun,opened,openRun,same⟩ := possible
  obtain ⟨draw,good⟩ := CommitMachine.supported o msg committed commitRun
  obtain ⟨e,run,done_⟩ := actual lower o (CommitKey.key draw) msg _ ps good.contents
  rw [run,support_pure,Set.mem_singleton_iff] at openRun
  rw [same,openRun]
  simp only [good.success,beq_self_eq_true,done_.1,Bool.and_self]

theorem secure (lower : LowerAll) : Artifact.submission.scheme.Hiding HIDING_ERROR :=
  OpeningView.secure (fun o k m t p _ stored => emits lower o k m t p stored)

end CommitGolfCandidate.Reconstruction.HonestDelivery
