import CommitGolfCandidate.P4OpenHeader
import CommitGolfCandidate.TwoPermutationPackedOpeningABI
import CommitGolfCandidate.TwoPermutationPackedOpeningProofBytes
import CommitGolfCandidate.TwoPermutationPackedOpeningModel

/-! P4 opener, end to end: the prefix leaves 04680e02's record-loop boundary at word 13 with a *virtual* trapdoor (the
trapdoor region of memory after the salts were materialised), and 04680e02's unchanged record writer and cap walk
(`PackedOpening.body_from_boundary`) produce the proof bytes of that virtual trapdoor. Ported from dadon's 2a19be00
`GroupOpenResume` and `GroupOpenFull`. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks machineMarks sortedIndex)
open PackedOpening (scheduledCycles proofLength OpenPhysical)
open TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 20000
set_option maxHeartbeats 1700000

theorem abi : PackedOpening.OpeningABI actual where
  toOpeningLayout := ⟨rfl,rfl,rfl,rfl⟩
  image := rfl
  capacity := by decide
  fuel := by decide

theorem boundary_at_end (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (p0 : 0<p.card) (r : Ready td p k s p.card) :
    PackedOpening.RecordBoundary actual (virtualTd s) p s 0 ∧ RecordMarks p s 0 := by
  have inp := virtual_input td p s (by
    intro a lo hi alg
    let w:=a/8
    have ea : a=8*w := by dsimp [w];omega
    have wlo : 738198020≤w := by dsimp [Opening.trapdoorBase,Opening.trapdoorBytes,LENGTH,LOG_LENGTH] at lo;omega
    have wlim : w<2^33 := by
      have lim : Opening.proofBase<2^36:=by decide
      omega
    have h:=r.frame w wlim (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr wlo)
    rw [ea];exact h)
  have start : s.pc=0x1034 := by simpa [passPC,address] using r.pc
  refine ⟨⟨?_,r.heap,?_,?_,?_,?_,inp,?_,?_,r.mark,r.cap,r.capLeaves,r.start⟩,?_⟩
  · simpa only [ite_eq_right (Nat.ne_of_lt p0)] using start
  · simpa using r.indices
  · exact r.salt.trans (by decide)
  · exact r.dest.trans (by decide)
  · exact r.leaves.trans (by decide)
  · simpa using r.count
  · exact r.base.trans (by decide)
  · intro node hn
    have stable := r.frame (512+node) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
    have z := PackedOpening.initial_mark_word actual actual_layout abi.image td p node hn
    have addr : BitVec.ofNat 64 (Opening.markBase+8*node)=wordAddress (512+node) := by
      unfold Opening.markBase wordAddress;congr 1 <;> omega
    have zz : memoryView (actual.initialState .opening (td,p)) (512+node)=0 := by simpa only [addr,memoryView] using z
    simpa [Opening.groupsBefore,machineMarks,addr,memoryView] using stable.trans zz

theorem kept_slice (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192) (s : MachineState)
    (r : Ready td p k s p.card) (off cells : Nat) (size : cells≤8) (a : off%8=0)
    (endAt : off+8*cells≤1342177280) :
    (virtualTd s).extractLsb' (8*off) (8*(8*cells))=td.extractLsb' (8*off) (8*(8*cells)) := by
  have room : off+8*cells≤Opening.trapdoorBytes := by change _≤1610612736;omega
  rw [virtual_slice s off _ (by rwa [actual_layout.trapdoorSize]),
    ←Opening.input_trapdoor_slice actual actual_layout td p off _ room]
  apply Opening.copied_buffer _ _ _ _ _ (by unfold Opening.trapdoorBase LENGTH LOG_LENGTH;omega)
    (by unfold Opening.trapdoorBase LENGTH LOG_LENGTH;omega) size
  intro i hi
  let w:=(Opening.trapdoorBase+off+8*i)/8
  have ea : Opening.trapdoorBase+off+8*i=8*w := by dsimp [w,Opening.trapdoorBase,LENGTH,LOG_LENGTH];omega
  have lower : 217≤w := by dsimp [w,Opening.trapdoorBase,LENGTH,LOG_LENGTH];omega
  have upper : w<704643588 := by dsimp [w,Opening.trapdoorBase,LENGTH,LOG_LENGTH];omega
  exact ea ▸ r.frame w (by omega) (Or.inr (by omega)) (Or.inr lower) (Or.inl upper)

/-- Every heap node of the virtual trapdoor is the original one (the prefix writes only the salt tape). -/
theorem kept_tree (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192) (s : MachineState)
    (r : Ready td p k s p.card) (n : Nat) (hi : n<2*LENGTH) :
    Opening.trapdoorHeap (s:=actual) (virtualTd s) n=Opening.trapdoorHeap (s:=actual) td n := by
  have v:=kept_slice td p k s r (32*n) 4 (by decide) (by omega)
    (by change n<2*16777216 at hi;omega)
  simpa only [Opening.trapdoorHeap,←Nat.mul_assoc] using v

theorem selected_salt (o : Oracle) (k : BitVec 192) (p : Positions) (s : MachineState)
    (seen : Seen o k p s p.card) (idx : Index) (member : idx∈p) :
    Opening.trapdoorSalt (s:=actual) (virtualTd s) idx=salts o.permutation k idx := by
  have iBound : idx.val<16777216:=idx.isLt
  have inList : idx∈p.sort (·≤·) := by simpa using member
  obtain ⟨j,hj,hx⟩:=List.mem_iff_getElem.mp inList
  have size : j<p.card := by simpa using hj
  have who : pos p j=idx := (pos_present p j size).trans hx
  unfold Opening.trapdoorSalt
  rw [virtual_slice s _ 16 (by change 80*16777216+16*idx.val+16≤1610612736;omega)]
  rw [show Opening.trapdoorBase+(80*LENGTH+16*idx.val)=8*(704643588+2*idx.val) by
    unfold Opening.trapdoorBase LENGTH LOG_LENGTH;omega]
  apply aligned_buffer_eq _ _ 16 (by decide)
  intro b hb
  have h:=seen j size (⟨b,hb⟩ : Fin 2)
  dsimp only at h;rw [who] at h
  have addr : destAt idx+BitVec.ofNat 64 (8*b)=wordAddress (704643588+2*idx.val+b) := by
    unfold destAt wordAddress;rw [←BitVec.ofNat_add];congr 1 <;> omega
  rw [addr] at h;exact h

private def leftOver (p : Positions) := actual.steps .opening-(28+passSteps p p.card 0+(scheduledCycles p-13))
private def recordsFuel (p : Positions) := scheduledCycles p-13+leftOver p

private theorem allowance (p : Positions) (nz : 0<p.card) :
    actual.steps .opening=28+(passSteps p p.card 0+recordsFuel p) := by
  have card : p.card≤16777216:=by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
  have b:=pass_steps_bound p p.card 0 (by omega)
  have budget:=PackedOpening.opening_cap_cycles_bound (Opening.groupsBefore p p.card)
  have notZero := Nat.ne_of_gt nz
  unfold recordsFuel leftOver;change 17179934720=_
  have h : scheduledCycles p≤13+596*p.card+20000 := by
    rw [scheduledCycles,if_neg notZero];omega
  change 17179934720=28+(passSteps p p.card 0+(scheduledCycles p-13+(17179934720-(28+passSteps p p.card 0+(scheduledCycles p-13)))))
  omega

private theorem run_from (s : Submission) (td : BitVec (8*s.sizes.trapdoor)) (p : Positions) (im : Image) (n : Nat)
    (hi : s.image .opening=im) (hf : s.steps .opening=n) :
    s.run .opening (td,p)=execute im n (s.initialState .opening (td,p)) true := by
  unfold Submission.run
  simp only [hi,hf,ite_true];rfl

attribute [local irreducible] execute passTrace passSteps header scheduledCycles fixedPass

theorem machine_run (hc : HeaderFacts) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    let initial:=actual.initialState .opening (td,p)
    actual.run .opening (td,p)=(do
      let s ← passTrace p p.card 0 (header initial)
      let z ← execute openingImage (recordsFuel p) s true
      return z.charge (28+passSteps p p.card 0+10*p.card) p.card) := by
  let init:=actual.initialState .opening (td,p)
  rw [run_from actual td p openingImage _ abi.image (allowance p nz),hc.run td p nz,
    pass_run td p (keyOf td) (header init) p.card 0 _ (hc.ready td p nz) (by omega)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro s;apply bind_congr;intro z;apply congrArg Pure.pure;cases z
  simp [Execution.charge,Nat.add_assoc]

theorem body_result (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card)
    (s : MachineState) (r : Ready td p (keyOf td) s p.card) :
    ∃ final, execute openingImage (recordsFuel p) s true=Pure.pure ⟨.success,final,scheduledCycles p-13,0⟩ ∧
      OpenPhysical actual (virtualTd s) p ⟨.success,final,scheduledCycles p,0⟩ :=
  PackedOpening.body_from_boundary (PackedOpening.execute_records_from_step PackedOpening.execute_record) actual abi
    (virtualTd s) p s nz (boundary_at_end td p _ s nz r).1 (boundary_at_end td p _ s nz r).2 (leftOver p)

theorem empty_result (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (empty : p.card=0) :
    ∃ z : Execution, actual.run .opening (td,p)=Pure.pure z ∧ z.exit=.success ∧ actual.openingSucceeded z=true ∧
      z.oracleCalls=0 ∧ z.cycles=7 ∧ actual.readProof z=[] := by
  let initial:=actual.initialState .opening (td,p)
  let t:=PackedOpening.exitPrefix (PackedOpening.setupPrefix initial 3) 3
  have run : actual.run .opening (td,p)=Pure.pure ⟨.success,t,7,0⟩ := by
    rw [run_from actual td p openingImage _ abi.image (show actual.steps .opening=7+(actual.steps .opening-7) by decide)]
    exact PackedOpening.execute_empty initial rfl _ true (by change BitVec.ofNat 64 p.card=0;rw [empty];rfl)
  have len : (t.getReg .x11).toNat=0 := by
    change ((PackedOpening.exitPrefix (PackedOpening.setupPrefix initial 3) 3).getReg .x11).toNat=0
    rw [PackedOpening.empty_proof_length];rfl
  refine ⟨_,run,rfl,?_,rfl,rfl,?_⟩
  · simp [Submission.openingSucceeded,len]
  · simp [Submission.readProof,Submission.openingSucceeded,len]

theorem all_resources (hc : HeaderFacts) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (z : Execution)
    (hit : z∈support (actual.run .opening (td,p))) :
    z.exit=.success ∧ actual.openingSucceeded z=true ∧
      (p.card=BATCH → z.cycles≤90391 ∧ (actual.readProof z).length≤68352) ∧ z.oracleCalls≤100*p.card := by
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
    let ref : Execution:=⟨.success,st,scheduledCycles p,0⟩
    have ok := PackedOpening.opening_success actual abi (virtualTd s) p ref phys
    refine ⟨rfl,ok,?_,by change p.card+0≤100*p.card;omega⟩
    intro batch
    have max:=PackedOpening.scheduled_scored_limits p batch
    have cap:=pass_steps_bound p p.card 0 (by omega)
    have k : p.card=128:=batch
    refine ⟨by change 28+passSteps p p.card 0+10*p.card+(scheduledCycles p-13)≤90391;omega,?_⟩
    have length : (actual.readProof ref).length=(st.getReg .x11).toNat := by
      simp only [Submission.readProof,ok,ite_true,List.length_map,List.length_range];rfl
    exact (length.trans phys.length).le.trans max.2

noncomputable def virtualFor (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :=
  if p.card=0 then td else virtualTd (fixedPass o p (keyOf td) p.card 0 (header (actual.initialState .opening (td,p))))

theorem fixed_open (hc : HeaderFacts) (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    fixedOracleRun o (actual.scheme.opening td p)=
      Pure.pure (PackedOpening.proofFromTrapdoor (s:=actual) (virtualFor o td p) p) := by
  change fixedOracleRun o (actual.readProof <$> actual.run .opening (td,p))=_
  rw [fixed_oracle_run_map]
  by_cases empty : p.card=0
  · obtain ⟨z,run,_,_,_,_,proof⟩:=empty_result td p empty
    rw [run,fixed_oracle_run_pure,map_pure,proof]
    have emp : p=∅:=Finset.card_eq_zero.mp empty;subst p
    simp [PackedOpening.proofFromTrapdoor,Opening.openingNodes]
  · have nz : 0<p.card := by omega
    let begin:=header (actual.initialState .opening (td,p))
    let st:=fixedPass o p (keyOf td) p.card 0 begin
    have start:= (hc.ready td p nz)
    have fixed := pass_fixed o td p (keyOf td) begin 0 p.card (by omega) start
    have seen : st∈support (passTrace p p.card 0 begin) := by
      apply writer_support (o.world.withAddCost Oracle.callCost) _ (st,p.card)
      change (_,_)∈support (o.run (passTrace p p.card 0 begin));rw [fixed];simp [st]
    have rd:=pass_post td p (keyOf td) begin st p.card 0 start (by omega) seen
    obtain ⟨last,body,phys⟩:=body_result td p nz st (by simpa using rd)
    rw [machine_run hc td p nz,fixed_oracle_run_bind]
    have proj : fixedOracleRun o (passTrace p p.card 0 begin)=Pure.pure st := by
      unfold fixedOracleRun;rw [fixed];rfl
    rw [proj,pure_bind,fixed_oracle_run_bind,body,fixed_oracle_run_pure,pure_bind,fixed_oracle_run_pure,map_pure]
    rw [virtualFor,if_neg empty]
    exact congrArg Pure.pure
      (PackedOpening.read_opening_proof actual abi (virtualTd st) p ⟨.success,last,scheduledCycles p,0⟩ phys)

end TwoPermutationPrototype.GroupedOpening
