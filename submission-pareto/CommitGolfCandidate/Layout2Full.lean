import CommitGolfCandidate.Layout2V2Facts
import CommitGolfCandidate.Machine
import CommitGolfCandidate.Layout2ProofBytes

/-! Layout 2 V2a opener, whole run: the 31-cycle header, the four-phase pass, then the record loop and the cap walk
(`l2_body`), against the V2a phase-writer guarantee `Layout2Phase2.PhaseFacts openingImage p`. Resources, the
128-position bounds (72,955 cycles, 72,160 bytes) and the deterministic opener (`fixed_open`: the proof is
`l2ProofFromPass` of the trapdoor and the pass's end state). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolfCandidate.Layout2Phase2 (PhaseFacts bodyLen)
open QuartetOpening (proofLength)
set_option maxRecDepth 18000
set_option maxHeartbeats 1700000

theorem l2abi : L2ABI actual := ⟨actual_layout,image_actual,by decide,by decide⟩
private def leftOver (p : Positions) := actual.steps .opening-(31+passSteps p p.card 0+(l2WideCycles p-15))
private def recordsFuel (p : Positions) := l2WideCycles p-15+leftOver p

theorem loop_cost_le (n : Nat) : loopCost n ≤ 205*n := by
  induction n with
  | zero => simp [loopCost]
  | succ n ih =>
    have : bodyLen (n%4) ≤ 197 := by unfold bodyLen; split_ifs <;> omega
    simp only [loopCost]; omega

theorem l2_wide_cycles_le (p : Positions) (nz : p.card ≠ 0) : l2WideCycles p ≤ 15+206*p.card+13300 := by
  have aligned : (recordBase p.card)%2=0 := by
    have : proofBase%2=0 := by decide
    unfold recordBase recordBytes; omega
  have cap := cap_walk_b_bound (Opening.groupsBefore p p.card) (recordBase p.card) aligned
  have lc := loop_cost_le p.card
  have ec : exitCost ((p.card+3)%4) ≤ 5 := by unfold exitCost; split_ifs <;> omega
  unfold l2WideCycles l2RecordsCost
  rw [if_neg nz]
  omega

private theorem allowance (p : Positions) (nz : 0<p.card) :
    actual.steps .opening=31+(passSteps p p.card 0+recordsFuel p) := by
  have card : p.card≤16777216:=card_le p
  have b:=pass_steps_bound p p.card 0
  have h:=l2_wide_cycles_le p (Nat.ne_of_gt nz)
  unfold recordsFuel leftOver;change 17179934720=_
  change 17179934720=31+(passSteps p p.card 0+(l2WideCycles p-15+(17179934720-(31+passSteps p p.card 0+(l2WideCycles p-15)))))
  omega

private theorem run_from (s : Submission) (td : BitVec (8*s.sizes.trapdoor)) (p : Positions) (im : Image) (n : Nat)
    (hi : s.image .opening=im) (hf : s.steps .opening=n) :
    s.run .opening (td,p)=execute im n (s.initialState .opening (td,p)) true := by
  unfold Submission.run
  simp only [hi,hf,ite_true];rfl

attribute [local irreducible] execute passTrace passSteps passCycles passCalls header2 l2WideCycles fixedPass

theorem machine_run (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    let initial:=actual.initialState .opening (td,p)
    actual.run .opening (td,p)=(do
      let s ← passTrace p p.card 0 (header2 initial)
      let z ← execute openingImage (recordsFuel p) s true
      return z.charge (31+passCycles p p.card 0) (passCalls p p.card 0)) := by
  let init:=actual.initialState .opening (td,p)
  rw [run_from actual td p openingImage _ l2abi.image (allowance p nz),certifiedHeader.run td p nz,
    pass_run td p (keyOf td) (header2 init) p.card 0 _ (certifiedHeader.ready td p nz) (by omega)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro s;apply bind_congr;intro z;apply congrArg Pure.pure;cases z
  simp [Execution.charge,Nat.add_assoc]

/-- The end of the pass: the record loop's start state, with the original trapdoor. -/
theorem start_at_end (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (p0 : 0<p.card) (r : Ready td p k s p.card) : L2Start actual td p s := by
  have card := card_le p
  have pb : proofBase=13824430176 := rfl
  have untouched (w : Nat) (h : 217≤w) (hw : w<2^33) (hb : w<proofBase/8) : ¬Touched p.card w := by
    rintro (x|x|⟨a,ha,x⟩)
    · omega
    · omega
    · have := pass_word_room a (by omega); omega
  have inp : SameOpeningInput (actual.initialState .opening (td,p)) s := by
    intro a lo hi alg
    let w:=a/8
    have ea : a=8*w := by dsimp [w];omega
    have wlo : 217≤w := by dsimp [trapdoorBase,trapdoorBytes,LENGTH,LOG_LENGTH] at lo;omega
    have wlim : w<2^33 := by
      have lim : proofBase<2^36:=by decide
      omega
    have h:=r.frame w wlim (untouched w wlo wlim (by omega))
    rw [ea]; exact h
  have start : s.pc=address 4096 := by simpa [passPC] using r.pc
  refine ⟨start, r.dest, ⟨r.heap,?_,r.salt,r.leaves,r.slots,?_,r.base,r.mark,
    (by rw [r.shift]; simpa using r.heap),r.capLeaves,r.start,inp,fun _ _ _ _ _ => rfl,?_,?_,?_⟩⟩
  · simpa using r.indices
  · rw [r.endReg]
    unfold indexAt
    congr 1
    have base : indicesBase = 9395245088 := rfl
    omega
  · intro a _ hk
    have ix := (posAt p a).isLt
    have room := pass_word_room a (by omega)
    have pw := r.pointer a hk
    have pm := pass_word_mul a
    rw [(pos_present p a hk).trans (pos_at_eq p a hk).symm] at pw
    have ea : BitVec.ofNat 64 (destOf a+16)=wordAddress (passWord a+2) := by
      have pd : passDest a=destOf a := rfl
      unfold wordAddress; congr 1; omega
    rw [ea]
    change memoryView s _=_
    rw [pw, quad_address_node]
    rfl
  · intro node hn
    have stable := r.frame (512+node) (by omega) (by
      rintro (x|x|⟨a,ha,x⟩)
      · omega
      · omega
      · have := pass_word_room a (by omega); omega)
    have z := initial_mark_word actual actual_layout image_actual td p node hn
    have addr : BitVec.ofNat 64 (Opening.markBase+8*node)=wordAddress (512+node) := by
      unfold Opening.markBase wordAddress;congr 1 <;> omega
    have zz : memoryView (actual.initialState .opening (td,p)) (512+node)=0 := by simpa only [addr,memoryView] using z
    simpa [Opening.groupsBefore,Opening.machineMarks,addr,memoryView] using stable.trans zz
  · intro i hi; exact absurd hi (Nat.not_lt_zero _)

theorem body_result (phases : ∀ p<4, PhaseFacts openingImage p) (td : BitVec (8*actual.sizes.trapdoor))
    (p : Positions) (nz : 0<p.card) (s : MachineState) (r : Ready td p (keyOf td) s p.card) :
    ∃ final, execute openingImage (recordsFuel p) s true=Pure.pure ⟨.success,final,l2WideCycles p-15,0⟩ ∧
      L2OpenPhysical actual td p s ⟨.success,final,l2WideCycles p,0⟩ :=
  l2_body phases actual l2abi td p s nz (start_at_end td p _ s nz r) (leftOver p)

theorem empty_result (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (empty : p.card=0) :
    ∃ z : Execution, actual.run .opening (td,p)=Pure.pure z ∧ z.exit=.success ∧ actual.openingSucceeded z=true ∧
      z.oracleCalls=0 ∧ z.cycles=8 ∧ actual.readProof z=[] := by
  let initial:=actual.initialState .opening (td,p)
  let t:=exitPrefix (emptyPrefix initial 4) 3
  have run : actual.run .opening (td,p)=Pure.pure ⟨.success,t,8,0⟩ := by
    rw [run_from actual td p openingImage _ l2abi.image (show actual.steps .opening=8+(actual.steps .opening-8) by decide)]
    exact execute_empty initial rfl _ true (by change BitVec.ofNat 64 p.card=0;rw [empty];rfl)
  have len : (t.getReg .x11).toNat=0 := by
    change ((exitPrefix (emptyPrefix initial 4) 3).getReg .x11).toNat=0
    rw [empty_proof_length];rfl
  refine ⟨_,run,rfl,?_,rfl,rfl,?_⟩
  · simp [Submission.openingSucceeded,len]
  · simp [Submission.readProof,Submission.openingSucceeded,len]

theorem l2_opening_success (s : Submission) (abi : L2ABI s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (pass : MachineState) (result : Execution)
    (physical : L2OpenPhysical s trapdoor positions pass result) :
    s.openingSucceeded result=true := by
  have bytes : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    exact (QuartetOpening.capacity_all positions).trans abi.capacity
  simp [Submission.openingSucceeded, physical.success, bytes]

/-- The 128-position bounds of the V2a opener after the pass. -/
theorem l2_scored_limits (positions : Positions) (count : positions.card=BATCH) :
    l2WideCycles positions ≤ 33001 ∧ proofLength positions ≤ 72160 := by
  have old := QuartetOpening.scored_limits positions count
  have nodes := Opening.opening_nodes_bound positions
  have k : positions.card=128 := count
  have frontier : Opening.openingNodes positions=
      Sampling.capFrontierNodes (Opening.groupsBefore positions positions.card) 1 8 := by
    unfold Opening.openingNodes
    rw [if_neg (by omega)]
  rw [frontier] at nodes
  exact ⟨l2_wide_cycles_batch positions count nodes, old.2⟩

theorem all_resources (phases : ∀ p<4, PhaseFacts openingImage p)
    (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (z : Execution)
    (hit : z∈support (actual.run .opening (td,p))) :
    z.exit=.success ∧ actual.openingSucceeded z=true ∧
      (p.card=BATCH → z.cycles≤72955 ∧ (actual.readProof z).length≤72160) ∧ z.oracleCalls≤100*p.card := by
  by_cases empty : p.card=0
  · obtain ⟨out,run,ex,ok,calls,_⟩:=empty_result td p empty
    rw [run,support_pure,Set.mem_singleton_iff] at hit;subst z
    exact ⟨ex,ok,fun h => False.elim (by change p.card=128 at h;omega),by rw [calls];omega⟩
  · have nz : 0<p.card := by omega
    rw [machine_run td p nz] at hit
    simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨s,pass,out,ran,rfl⟩:=hit
    have rd:=pass_post td p _ _ _ p.card 0 (certifiedHeader.ready td p nz) (by omega) pass
    obtain ⟨st,body,phys⟩:=body_result phases td p nz s (by simpa using rd)
    rw [body,support_pure,Set.mem_singleton_iff] at ran;subst out
    let ref : Execution:=⟨.success,st,l2WideCycles p,0⟩
    have ok := l2_opening_success actual l2abi td p s ref phys
    have callBound:=pass_calls_bound p p.card 0
    refine ⟨rfl,ok,?_,by change passCalls p p.card 0+0≤100*p.card;omega⟩
    intro batch
    have max:=l2_scored_limits p batch
    have cap:=pass_cycles_bound p p.card 0 (by omega)
    have k : p.card=128:=batch
    refine ⟨by change 31+passCycles p p.card 0+(l2WideCycles p-15)≤72955;omega,?_⟩
    have length : (actual.readProof ref).length=(st.getReg .x11).toNat := by
      simp only [Submission.readProof,ok,ite_true,List.length_map,List.length_range];rfl
    exact (length.trans phys.length).le.trans max.2

theorem pass_proof_empty (td : BitVec (8*actual.sizes.trapdoor)) (pass : MachineState) :
    l2ProofFromPass (s:=actual) td pass ∅=[] := by
  simp [l2ProofFromPass, l2Proof2, physFlush, flushLen, Opening.openingNodes, fold_nodes_nil]

/-- The V2a opener is deterministic: its proof is `l2ProofFromPass` of the trapdoor and the pass's end state. -/
theorem fixed_open (phases : ∀ p<4, PhaseFacts openingImage p) (o : Oracle)
    (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    fixedOracleRun o (actual.scheme.opening td p)=Pure.pure (l2ProofFromPass (s:=actual) td (passEnd o td p) p) := by
  change fixedOracleRun o (actual.readProof <$> actual.run .opening (td,p))=_
  rw [fixed_oracle_run_map]
  by_cases empty : p.card=0
  · obtain ⟨z,run,_,_,_,_,proof⟩:=empty_result td p empty
    rw [run,fixed_oracle_run_pure,map_pure,proof]
    have emp : p=∅:=Finset.card_eq_zero.mp empty;subst p
    rw [pass_proof_empty]
  · have nz : 0<p.card := by omega
    let begin:=header2 (actual.initialState .opening (td,p))
    let st:=fixedPass o p (keyOf td) p.card 0 begin
    have start := certifiedHeader.ready td p nz
    have fixed := pass_fixed o td p (keyOf td) begin 0 p.card (by omega) start
    have seen : st∈support (passTrace p p.card 0 begin) := by
      apply writer_support (o.world.withAddCost Oracle.callCost) _ (st,passCalls p p.card 0)
      change (_,_)∈support (o.run (passTrace p p.card 0 begin));rw [fixed];simp [st]
    have rd:=pass_post td p (keyOf td) begin st p.card 0 start (by omega) seen
    obtain ⟨last,body,phys⟩:=body_result phases td p nz st (by simpa using rd)
    rw [machine_run td p nz,fixed_oracle_run_bind]
    have proj : fixedOracleRun o (passTrace p p.card 0 begin)=Pure.pure st := by
      unfold fixedOracleRun;rw [fixed];rfl
    rw [proj,pure_bind,fixed_oracle_run_bind,body,fixed_oracle_run_pure,pure_bind,fixed_oracle_run_pure,map_pure]
    exact congrArg Pure.pure (read_l2_proof actual l2abi td p st ⟨.success,last,l2WideCycles p,0⟩ phys)

end TwoPermutationPrototype.GroupedOpening.Layout2V2
