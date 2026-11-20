import CommitGolfCandidate.GroupOpenHeaderSpec
import CommitGolfCandidate.GroupOpenResume
import CommitGolfCandidate.K3OpenFacts
import CommitGolfCandidate.Machine

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open QuartetOpening (proofLength)
set_option maxRecDepth 18000
set_option maxHeartbeats 1700000

theorem abi : OpeningABI actual := ⟨actual_layout,image_actual,by decide,by decide⟩
private def leftOver (p : Positions) := actual.steps .opening-(36+passSteps p p.card 0+(wideCycles p-15))
private def recordsFuel (p : Positions) := wideCycles p-15+leftOver p

/-- One position of the pass takes at most 167 steps (at most 30 head, 52 chain, 16 post). -/
theorem per_steps_le (i : Index) (left last : Nat) : perSteps i left last≤167 := by
  have links : chainLinks i<34 := by unfold chainLinks;omega
  unfold perSteps headSteps chainSteps postSteps
  split_ifs <;> omega

theorem pass_steps_bound (p : Positions) (n j : Nat) : passSteps p n j≤167*n := by
  induction n generalizing j with
  | zero => simp [passSteps]
  | succ n ih =>
    rw [passSteps]
    have h:=ih (j+1)
    have one:=per_steps_le (pos p j) (p.card-j) (lastOf p j)
    omega

private theorem allowance (p : Positions) (nz : 0<p.card) :
    actual.steps .opening=36+(passSteps p p.card 0+recordsFuel p) := by
  have card : p.card≤16777216:=by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
  have b:=pass_steps_bound p p.card 0
  have h:=wide_cycles_le p (Nat.ne_of_gt nz)
  unfold recordsFuel leftOver;change 17179934720=_
  change 17179934720=36+(passSteps p p.card 0+(wideCycles p-15+(17179934720-(36+passSteps p p.card 0+(wideCycles p-15)))))
  omega

private theorem run_from (s : Submission) (td : BitVec (8*s.sizes.trapdoor)) (p : Positions) (im : Image) (n : Nat)
    (hi : s.image .opening=im) (hf : s.steps .opening=n) :
    s.run .opening (td,p)=execute im n (s.initialState .opening (td,p)) true := by
  unfold Submission.run
  simp only [hi,hf,ite_true];rfl

attribute [local irreducible] execute passTrace passSteps passCycles passCalls header wideCycles fixedPass

theorem machine_run (hc : HeaderFacts) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    let initial:=actual.initialState .opening (td,p)
    actual.run .opening (td,p)=(do
      let s ← passTrace p p.card 0 (header initial)
      let z ← execute openingImage (recordsFuel p) s true
      return z.charge (36+passCycles p p.card 0) (passCalls p p.card 0)) := by
  let init:=actual.initialState .opening (td,p)
  rw [run_from actual td p openingImage _ abi.image (allowance p nz),hc.run td p nz,pass_run td p (keyOf td) (header init) p.card 0 _ (hc.ready td p nz) (by omega)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro s;apply bind_congr;intro z;apply congrArg Pure.pure;cases z
  simp [Execution.charge,Nat.add_assoc]

theorem body_result (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card)
    (s : MachineState) (r : Ready td p (keyOf td) s p.card) :
    ∃ final, execute openingImage (recordsFuel p) s true=Pure.pure ⟨.success,final,wideCycles p-15,0⟩ ∧
      OpenPhysical actual (virtualTd s) p ⟨.success,final,wideCycles p,0⟩ :=
  body_from_boundary (execute_records_from_step execute_record) actual abi (virtualTd s) p s nz
    (boundary_at_end td p _ s nz r).1 (boundary_at_end td p _ s nz r).2 (leftOver p)

theorem empty_result (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (empty : p.card=0) :
    ∃ z : Execution, actual.run .opening (td,p)=Pure.pure z ∧ z.exit=.success ∧ actual.openingSucceeded z=true ∧
      z.oracleCalls=0 ∧ z.cycles=7 ∧ actual.readProof z=[] := by
  let initial:=actual.initialState .opening (td,p)
  let t:=exitPrefix (setupPrefix initial 3) 3
  have run : actual.run .opening (td,p)=Pure.pure ⟨.success,t,7,0⟩ := by
    rw [run_from actual td p openingImage _ abi.image (show actual.steps .opening=7+(actual.steps .opening-7) by decide)]
    exact execute_empty initial rfl _ true (by change BitVec.ofNat 64 p.card=0;rw [empty];rfl)
  have len : (t.getReg .x11).toNat=0 := by
    change ((exitPrefix (setupPrefix initial 3) 3).getReg .x11).toNat=0
    rw [empty_proof_length];rfl
  refine ⟨_,run,rfl,?_,rfl,rfl,?_⟩
  · simp [Submission.openingSucceeded,len]
  · simp [Submission.readProof,Submission.openingSucceeded,len]

theorem all_resources (hc : HeaderFacts) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (z : Execution)
    (hit : z∈support (actual.run .opening (td,p))) :
    z.exit=.success ∧ actual.openingSucceeded z=true ∧
      (p.card=BATCH → z.cycles≤118593 ∧ (actual.readProof z).length≤72160) ∧ z.oracleCalls≤100*p.card := by
  by_cases empty : p.card=0
  · obtain ⟨out,run,ex,ok,calls,_⟩:=empty_result td p empty
    rw [run,support_pure,Set.mem_singleton_iff] at hit;subst z
    exact ⟨ex,ok,fun h => False.elim (by change p.card=128 at h;omega),by rw [calls];omega⟩
  · have nz : 0<p.card := by omega
    rw [machine_run hc td p nz] at hit
    simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨s,pass,out,ran,rfl⟩:=hit
    have rd:=pass_post td p _ _ _ p.card 0 (hc.ready td p nz) (by omega) pass
    obtain ⟨st,body,phys⟩:=body_result td p nz s (by simpa using rd)
    rw [body,support_pure,Set.mem_singleton_iff] at ran;subst out
    let ref : Execution:=⟨.success,st,wideCycles p,0⟩
    have ok := opening_success actual abi (virtualTd s) p ref phys
    have callBound:=pass_calls_bound p p.card 0
    refine ⟨rfl,ok,?_,by change passCalls p p.card 0+0≤100*p.card;omega⟩
    intro batch
    have max:=wide_scored_limits p batch
    have cap:=pass_cycles_bound p p.card 0 (by omega)
    have k : p.card=128:=batch
    refine ⟨by change 36+passCycles p p.card 0+(wideCycles p-15)≤118593;omega,?_⟩
    have length : (actual.readProof ref).length=(st.getReg .x11).toNat := by
      simp only [Submission.readProof,ok,ite_true,List.length_map,List.length_range];rfl
    exact (length.trans phys.length).le.trans max.2

theorem fixed_open (hc : HeaderFacts) (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    fixedOracleRun o (actual.scheme.opening td p)=Pure.pure (proofFromTrapdoor (s:=actual) (virtualFor o td p) p) := by
  change fixedOracleRun o (actual.readProof <$> actual.run .opening (td,p))=_
  rw [fixed_oracle_run_map]
  by_cases empty : p.card=0
  · obtain ⟨z,run,_,_,_,_,proof⟩:=empty_result td p empty
    rw [run,fixed_oracle_run_pure,map_pure,proof]
    have emp : p=∅:=Finset.card_eq_zero.mp empty;subst p
    simp [proofFromTrapdoor,Opening.openingNodes,fold_nodes_nil]
  · have nz : 0<p.card := by omega
    let begin:=header (actual.initialState .opening (td,p))
    let st:=fixedPass o p (keyOf td) p.card 0 begin
    have start:= (hc.ready td p nz)
    have fixed := pass_fixed o td p (keyOf td) begin 0 p.card (by omega) start
    have seen : st∈support (passTrace p p.card 0 begin) := by
      apply writer_support (o.world.withAddCost Oracle.callCost) _ (st,passCalls p p.card 0)
      change (_,_)∈support (o.run (passTrace p p.card 0 begin));rw [fixed];simp [st]
    have rd:=pass_post td p (keyOf td) begin st p.card 0 start (by omega) seen
    obtain ⟨last,body,phys⟩:=body_result td p nz st (by simpa using rd)
    rw [machine_run hc td p nz,fixed_oracle_run_bind]
    have proj : fixedOracleRun o (passTrace p p.card 0 begin)=Pure.pure st := by
      unfold fixedOracleRun;rw [fixed];rfl
    rw [proj,pure_bind,fixed_oracle_run_bind,body,fixed_oracle_run_pure,pure_bind,fixed_oracle_run_pure,map_pure]
    rw [virtualFor,if_neg empty]
    exact congrArg Pure.pure (read_opening_proof actual abi (virtualTd st) p ⟨.success,last,wideCycles p,0⟩ phys)

end TwoPermutationPrototype.GroupedOpening
