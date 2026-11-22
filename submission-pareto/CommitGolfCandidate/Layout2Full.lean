import CommitGolfCandidate.Layout2V2Facts
import CommitGolfCandidate.Machine
import CommitGolfCandidate.Layout2ProofBytes

/-! Layout 2 V2b opener, whole run: the 31-cycle header, the four-phase pass, then the record loop and the cap stage
(`l2_body`), against the V2a phase-writer guarantee `Layout2Phase2.PhaseFacts openingImage p` (V2b body words) and
the cap stage's `Layout2CapStage.CapStage capRaw`. Resources, the 128-position bounds (69,329 cycles, 72,160 bytes)
and the deterministic opener (`fixed_open`: the proof is `l2bProofFromPass capRaw` of the trapdoor and the pass's end
state). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolfCandidate.Layout2Phase2 (PhaseFacts bodyLen)
open CommitGolfCandidate.Layout2CapStage (CapStage frontierDigests)
open QuartetOpening (proofLength)
set_option maxRecDepth 18000
set_option maxHeartbeats 1700000

theorem l2abi : L2ABI actual := ⟨actual_layout,image_actual,by decide,by decide⟩
/-- The fuel after the header and the pass. -/
private def restFuel (p : Positions) := actual.steps .opening-(31+passSteps p p.card 0)

theorem loop_cost_le (n : Nat) : loopCost n ≤ 205*n := by
  induction n with
  | zero => simp [loopCost]
  | succ n ih =>
    have : bodyLen (n%4) ≤ 197 := by unfold bodyLen; split_ifs <;> omega
    simp only [loopCost]; omega

theorem records_cost_le (k : Nat) : l2RecordsCost k ≤ 205*k+5 := by
  have := loop_cost_le k
  have : exitCost ((k+3)%4) ≤ 5 := by unfold exitCost; split_ifs <;> omega
  unfold l2RecordsCost; omega

private theorem allowance (p : Positions) : actual.steps .opening=31+(passSteps p p.card 0+restFuel p) := by
  have card : p.card≤16777216:=card_le p
  have b:=pass_steps_bound p p.card 0
  unfold restFuel;change 17179934720=_
  change 17179934720=31+(passSteps p p.card 0+(17179934720-(31+passSteps p p.card 0)))
  omega

private theorem rest_room (p : Positions) (steps : Nat) (hs : steps ≤ 2^30) :
    l2RecordsCost p.card+steps ≤ restFuel p := by
  have card : p.card≤16777216:=card_le p
  have b:=pass_steps_bound p p.card 0
  have r:=records_cost_le p.card
  unfold restFuel;change _ ≤ 17179934720-_
  omega

private theorem run_from (s : Submission) (td : BitVec (8*s.sizes.trapdoor)) (p : Positions) (im : Image) (n : Nat)
    (hi : s.image .opening=im) (hf : s.steps .opening=n) :
    s.run .opening (td,p)=execute im n (s.initialState .opening (td,p)) true := by
  unfold Submission.run
  simp only [hi,hf,ite_true];rfl

attribute [local irreducible] execute passTrace passSteps passCycles passCalls header2 fixedPass

theorem machine_run (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    let initial:=actual.initialState .opening (td,p)
    actual.run .opening (td,p)=(do
      let s ← passTrace p p.card 0 (header2 initial)
      let z ← execute openingImage (restFuel p) s true
      return z.charge (31+passCycles p p.card 0) (passCalls p p.card 0)) := by
  let init:=actual.initialState .opening (td,p)
  rw [run_from actual td p openingImage _ l2abi.image (allowance p),certifiedHeader.run td p nz,
    pass_run td p (keyOf td) (header2 init) p.card 0 _ (certifiedHeader.ready td p nz) (by omega)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro s;apply bind_congr;intro z;apply congrArg Pure.pure;cases z
  simp [Execution.charge,Nat.add_assoc]

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
  · -- the byte marks start at zero: their dwords are zero in the loaded input and the pass leaves them
    intro i hi
    have hn : 32+i/8<512 := by omega
    have stable := r.frame (512+(32+i/8)) (by omega) (by
      rintro (x|x|⟨a,ha,x⟩)
      · omega
      · omega
      · have := pass_word_room a (by omega); omega)
    have z := initial_mark_word actual actual_layout image_actual td p (32+i/8) hn
    have addr : BitVec.ofNat 64 (Opening.markBase+8*(32+i/8))=wordAddress (512+(32+i/8)) := by
      unfold Opening.markBase wordAddress;congr 1 <;> omega
    have zz : memoryView (actual.initialState .opening (td,p)) (512+(32+i/8))=0 := by simpa only [addr,memoryView] using z
    have w0 : s.getMem (BitVec.ofNat 64 (Opening.markBase+8*(32+i/8)))=0 := by
      rw [addr]; exact stable.trans zz
    have al : alignToDword (BitVec.ofNat 64 (Opening.markBase+256+i))=BitVec.ofNat 64 (Opening.markBase+8*(32+i/8)) := by
      rw [table_align_eq (Opening.markBase+256+i) (by unfold Opening.markBase; omega)]; congr 1; unfold Opening.markBase; omega
    unfold MachineState.getByte
    rw [al, w0]
    simp [Opening.groupsBefore, Sampling.capIsMarked, extractByte]
  · intro i hi; exact absurd hi (Nat.not_lt_zero _)

theorem body_result (phases : ∀ p<4, PhaseFacts openingImage p) (capRaw : List (BitVec 256) → List Byte)
    (cap : CapStage capRaw) (td : BitVec (8*actual.sizes.trapdoor))
    (p : Positions) (nz : 0<p.card) (s : MachineState) (r : Ready td p (keyOf td) s p.card) :
    ∃ final cycles, execute openingImage (restFuel p) s true=Pure.pure ⟨.success,final,l2RecordsCost p.card+cycles,0⟩ ∧
      (p.card=128 → cycles ≤ 3407) ∧
      L2OpenPhysical actual capRaw td p s ⟨.success,final,l2RecordsCost p.card+cycles,0⟩ := by
  obtain ⟨final,steps,cycles,sb,cb,ran,phys⟩:=l2_body phases capRaw cap actual l2abi td p s nz (start_at_end td p _ s nz r)
  have room:=rest_room p steps sb
  refine ⟨final,cycles,?_,cb,phys⟩
  rw [show restFuel p=l2RecordsCost p.card+steps+(restFuel p-(l2RecordsCost p.card+steps)) by omega]
  exact ran _

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

theorem l2_opening_success (s : Submission) (abi : L2ABI s) (capRaw : List (BitVec 256) → List Byte)
    (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (pass : MachineState) (result : Execution)
    (physical : L2OpenPhysical s capRaw trapdoor positions pass result) :
    s.openingSucceeded result=true := by
  have bytes : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    exact (QuartetOpening.capacity_all positions).trans abi.capacity
  simp [Submission.openingSucceeded, physical.success, bytes]

theorem all_resources (phases : ∀ p<4, PhaseFacts openingImage p) (capRaw : List (BitVec 256) → List Byte)
    (cap : CapStage capRaw) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (z : Execution)
    (hit : z∈support (actual.run .opening (td,p))) :
    z.exit=.success ∧ actual.openingSucceeded z=true ∧
      (p.card=BATCH → z.cycles≤69329 ∧ (actual.readProof z).length≤72160) ∧ z.oracleCalls≤100*p.card := by
  by_cases empty : p.card=0
  · obtain ⟨out,run,ex,ok,calls,_⟩:=empty_result td p empty
    rw [run,support_pure,Set.mem_singleton_iff] at hit;subst z
    exact ⟨ex,ok,fun h => False.elim (by change p.card=128 at h;omega),by rw [calls];omega⟩
  · have nz : 0<p.card := by omega
    rw [machine_run td p nz] at hit
    simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨s,pass,out,ran,rfl⟩:=hit
    have rd:=pass_post td p _ _ _ p.card 0 (certifiedHeader.ready td p nz) (by omega) pass
    obtain ⟨st,cycles,body,cb,phys⟩:=body_result phases capRaw cap td p nz s (by simpa using rd)
    rw [body,support_pure,Set.mem_singleton_iff] at ran;subst out
    let ref : Execution:=⟨.success,st,l2RecordsCost p.card+cycles,0⟩
    have ok := l2_opening_success actual l2abi capRaw td p s ref phys
    have callBound:=pass_calls_bound p p.card 0
    refine ⟨rfl,ok,?_,by change passCalls p p.card 0+0≤100*p.card;omega⟩
    intro batch
    have k : p.card=128:=batch
    have rc : l2RecordsCost p.card=25953 := by rw [k]; exact records_cost_batch
    have cyc:=pass_cycles_bound p p.card 0 (by omega)
    have cc:=cb k
    refine ⟨by change 31+passCycles p p.card 0+(l2RecordsCost p.card+cycles)≤69329;omega,?_⟩
    have length : (actual.readProof ref).length=(st.getReg .x11).toNat := by
      simp only [Submission.readProof,ok,ite_true,List.length_map,List.length_range];rfl
    exact (length.trans phys.length).le.trans (QuartetOpening.scored_limits p batch).2

theorem pass_proof_empty (capRaw : List (BitVec 256) → List Byte) (cap : CapStage capRaw)
    (td : BitVec (8*actual.sizes.trapdoor)) (pass : MachineState) :
    l2bProofFromPass (s:=actual) capRaw td pass ∅=[] := by
  have nil : capRaw []=[] := List.eq_nil_of_length_eq_zero (by rw [cap.length]; rfl)
  simp [l2bProofFromPass, l2Proof2, physFlush, flushLen, frontierDigests, Opening.openingNodes, nil]

/-- The V2b opener is deterministic: its proof is `l2bProofFromPass capRaw` of the trapdoor and the pass's end
state. -/
theorem fixed_open (phases : ∀ p<4, PhaseFacts openingImage p) (capRaw : List (BitVec 256) → List Byte)
    (cap : CapStage capRaw) (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    fixedOracleRun o (actual.scheme.opening td p)=
      Pure.pure (l2bProofFromPass (s:=actual) capRaw td (passEnd o td p) p) := by
  change fixedOracleRun o (actual.readProof <$> actual.run .opening (td,p))=_
  rw [fixed_oracle_run_map]
  by_cases empty : p.card=0
  · obtain ⟨z,run,_,_,_,_,proof⟩:=empty_result td p empty
    rw [run,fixed_oracle_run_pure,map_pure,proof]
    have emp : p=∅:=Finset.card_eq_zero.mp empty;subst p
    rw [pass_proof_empty capRaw cap]
  · have nz : 0<p.card := by omega
    let begin:=header2 (actual.initialState .opening (td,p))
    let st:=fixedPass o p (keyOf td) p.card 0 begin
    have start := certifiedHeader.ready td p nz
    have fixed := pass_fixed o td p (keyOf td) begin 0 p.card (by omega) start
    have seen : st∈support (passTrace p p.card 0 begin) := by
      apply writer_support (o.world.withAddCost Oracle.callCost) _ (st,passCalls p p.card 0)
      change (_,_)∈support (o.run (passTrace p p.card 0 begin));rw [fixed];simp [st]
    have rd:=pass_post td p (keyOf td) begin st p.card 0 start (by omega) seen
    obtain ⟨last,cycles,body,_,phys⟩:=body_result phases capRaw cap td p nz st (by simpa using rd)
    rw [machine_run td p nz,fixed_oracle_run_bind]
    have proj : fixedOracleRun o (passTrace p p.card 0 begin)=Pure.pure st := by
      unfold fixedOracleRun;rw [fixed];rfl
    rw [proj,pure_bind,fixed_oracle_run_bind,body,fixed_oracle_run_pure,pure_bind,fixed_oracle_run_pure,map_pure]
    exact congrArg Pure.pure
      (read_l2b_proof actual l2abi capRaw td p st ⟨.success,last,l2RecordsCost p.card+cycles,0⟩ phys)

end TwoPermutationPrototype.GroupedOpening.Layout2V2
