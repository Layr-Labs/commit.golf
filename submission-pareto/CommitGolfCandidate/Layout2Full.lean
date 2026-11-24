import CommitGolfCandidate.Layout2V2Facts
import CommitGolfCandidate.Layout2FusedHeader
import CommitGolfCandidate.Machine
import CommitGolfCandidate.Layout2ProofBytes

/-! Layout 2 V2 opener with the fused loop (Increment 4b), without the one-byte trim, whole run: the 31-cycle header,
the fused four-phase loop (`Layout2FusedLoop`), its exit stub, then the cap stage (`l2_cap`), against the cap stage's
`Layout2CapStage.CapStage capRaw`. Resources, the 128-position bounds (68,558 cycles, 72,160 bytes) and the
deterministic opener (`fixed_open`: the proof is `l2bProofFromPass capRaw` of the trapdoor and the reference pass state
`passEnd`). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolfCandidate.Layout2Phase2 (bodyLen)
open TwoPermutationPrototype.GroupedOpening.Layout2F (Ready loopTrace loopSteps loopCycles loopCalls header2)
open CommitGolfCandidate.Layout2CapStage (CapStage frontierDigests)
open QuartetOpening (proofLength)
set_option maxRecDepth 18000
set_option maxHeartbeats 1700000

theorem l2abi : L2ABI actual := ⟨actual_layout,image_actual,by decide,by decide⟩
/-- The fuel after the header and the loop. -/
private def restFuel (p : Positions) := actual.steps .opening-(31+loopSteps p p.card 0)

private theorem allowance (p : Positions) : actual.steps .opening=31+(loopSteps p p.card 0+restFuel p) := by
  have card : p.card≤16777216:=card_le p
  have b:=Layout2F.loop_steps_bound p p.card 0
  unfold restFuel;change 17179934720=_
  change 17179934720=31+(loopSteps p p.card 0+(17179934720-(31+loopSteps p p.card 0)))
  omega

private theorem rest_room (p : Positions) (steps : Nat) (hs : steps ≤ 2^30) :
    exitCost ((p.card+3)%4)+steps ≤ restFuel p := by
  have card : p.card≤16777216:=card_le p
  have b:=Layout2F.loop_steps_bound p p.card 0
  have e : exitCost ((p.card+3)%4) ≤ 5 := by unfold exitCost; split_ifs <;> omega
  unfold restFuel;change _ ≤ 17179934720-_
  omega

private theorem run_from (s : Submission) (td : BitVec (8*s.sizes.trapdoor)) (p : Positions) (im : Image) (n : Nat)
    (hi : s.image .opening=im) (hf : s.steps .opening=n) :
    s.run .opening (td,p)=execute im n (s.initialState .opening (td,p)) true := by
  unfold Submission.run
  simp only [hi,hf,ite_true];rfl

attribute [local irreducible] execute loopTrace loopSteps loopCycles loopCalls header2 Layout2F.fixedLoop

theorem machine_run (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    let initial:=actual.initialState .opening (td,p)
    actual.run .opening (td,p)=(do
      let s ← loopTrace p p.card 0 (header2 initial)
      let z ← execute openingImage (restFuel p) s true
      return z.charge (31+loopCycles p p.card 0) (loopCalls p p.card 0)) := by
  let init:=actual.initialState .opening (td,p)
  rw [run_from actual td p openingImage _ l2abi.image (allowance p),Layout2F.header_run td p nz,
    Layout2F.loop_run td p (keyOf td) (header2 init) p.card 0 _ (Layout2F.header_valid td p nz).2 (by omega)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro s;apply bind_congr;intro z;apply congrArg Pure.pure;cases z
  simp [Execution.charge,Nat.add_assoc]

/-- From the loop's end: the exit stub, then the cap stage. `pass` is any state that agrees with the loop's end state
on the bytes the writers keep. -/
theorem body_result (capRaw : List (BitVec 256) → List Byte)
    (cap : CapStage capRaw) (td : BitVec (8*actual.sizes.trapdoor))
    (p : Positions) (nz : 0<p.card) (s pass : MachineState) (r : Ready td p (keyOf td) s p.card)
    (retained : ∀ j<p.card, ∀ b<Layout2Phase.stride (j%4), Layout2Phase2.written ((posAt p j).val%4) (b/8)=false →
      s.getByte (BitVec.ofNat 64 (destOf j+b))=pass.getByte (BitVec.ofNat 64 (destOf j+b))) :
    ∃ final cycles, execute openingImage (restFuel p) s true=
        Pure.pure ⟨.success,final,exitCost ((p.card+3)%4)+cycles,0⟩ ∧
      (p.card=128 → cycles ≤ 3375) ∧
      L2OpenPhysical actual capRaw td p pass ⟨.success,final,exitCost ((p.card+3)%4)+cycles,0⟩ := by
  obtain ⟨lower,ranExit,done⟩ := Layout2F.exit_done td p (keyOf td) s pass r nz retained
  obtain ⟨final,steps,cycles,sb,cb,ran,phys⟩:=l2_cap capRaw cap actual l2abi td p pass lower nz done
  have room:=rest_room p steps sb
  refine ⟨final,cycles,?_,cb,?_⟩
  · rw [show restFuel p=exitCost ((p.card+3)%4)+(steps+(restFuel p-(exitCost ((p.card+3)%4)+steps))) by omega,
      ranExit _ true, ran _]
    simp [Execution.charge]
  · exact ⟨phys.success,phys.length,phys.noCalls,phys.lower,phys.flush,phys.footer⟩

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

/-- With 128 positions the proof has at most 72,160 bytes: `534 · 128 + capOffset f` with at most 128 frontier nodes. -/
theorem scored_full (p : Positions) (k : p.card=128) : QuartetOpening.proofLength p ≤ 72160 := by
  have split := proof_length_split p
  have nb := Opening.opening_nodes_bound p
  rw [split,k]
  unfold capOffset
  omega

theorem all_resources (capRaw : List (BitVec 256) → List Byte)
    (cap : CapStage capRaw) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (z : Execution)
    (hit : z∈support (actual.run .opening (td,p))) :
    z.exit=.success ∧ actual.openingSucceeded z=true ∧
      (p.card=BATCH → z.cycles≤68558 ∧ (actual.readProof z).length≤72160) ∧ z.oracleCalls≤100*p.card := by
  by_cases empty : p.card=0
  · obtain ⟨out,run,ex,ok,calls,_⟩:=empty_result td p empty
    rw [run,support_pure,Set.mem_singleton_iff] at hit;subst z
    exact ⟨ex,ok,fun h => False.elim (by change p.card=128 at h;omega),by rw [calls];omega⟩
  · have nz : 0<p.card := by omega
    rw [machine_run td p nz] at hit
    simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨s,pass,out,ran,rfl⟩:=hit
    have rd:=Layout2F.loop_post td p _ _ _ p.card 0 (Layout2F.header_valid td p nz).2 (by omega) pass
    obtain ⟨st,cycles,body,cb,phys⟩:=body_result capRaw cap td p nz s s (by simpa using rd) (fun _ _ _ _ _ => rfl)
    rw [body,support_pure,Set.mem_singleton_iff] at ran;subst out
    let ref : Execution:=⟨.success,st,exitCost ((p.card+3)%4)+cycles,0⟩
    have ok := l2_opening_success actual l2abi capRaw td p s ref phys
    have callBound:=Layout2F.loop_calls_bound p p.card 0
    refine ⟨rfl,ok,?_,by change loopCalls p p.card 0+0≤100*p.card;omega⟩
    intro batch
    have k : p.card=128:=batch
    have cyc:=Layout2F.loop_cycles_bound p p.card 0
    rw [k, Layout2F.cost_128] at cyc
    have ec : exitCost ((p.card+3)%4)=1 := by rw [k]; rfl
    have cc:=cb k
    refine ⟨by change 31+loopCycles p p.card 0+(exitCost ((p.card+3)%4)+cycles)≤68558;rw [ec, k];omega,?_⟩
    have length : (actual.readProof ref).length=(st.getReg .x11).toNat := by
      simp only [Submission.readProof,ok,ite_true,List.length_map,List.length_range];rfl
    show (actual.readProof ref).length ≤ 72160
    rw [length,phys.length]
    exact scored_full p k

theorem pass_proof_empty (capRaw : List (BitVec 256) → List Byte) (cap : CapStage capRaw)
    (td : BitVec (8*actual.sizes.trapdoor)) (pass : MachineState) :
    l2bProofFromPass (s:=actual) capRaw td pass ∅=[] := by
  have nil : capRaw []=[] := List.eq_nil_of_length_eq_zero (by rw [cap.length]; rfl)
  simp [l2bProofFromPass, l2Proof2, physFlush, flushLen, frontierDigests, Opening.openingNodes, nil]

/-- The fused opener is deterministic: its proof is `l2bProofFromPass capRaw` of the trapdoor and the reference pass
state `passEnd`. -/
theorem fixed_open (capRaw : List (BitVec 256) → List Byte)
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
    let st:=Layout2F.fixedLoop o p (keyOf td) p.card 0 begin
    have start := (Layout2F.header_valid td p nz).2
    have fixed := Layout2F.loop_fixed o td p (keyOf td) begin 0 p.card (by omega) start
    have rd := Layout2F.fixed_post o td p (keyOf td) begin 0 p.card (by omega) start
    have sn := Layout2F.seen_loop o td p (keyOf td) begin 0 p.card (by omega) start (Layout2F.rseen_zero o _ td p _)
    rw [Nat.zero_add] at rd sn
    obtain ⟨last,cycles,body,_,phys⟩:=body_result capRaw cap td p nz st (passEnd o td p) rd
      (Layout2F.fused_retained o td p st sn)
    rw [machine_run td p nz,fixed_oracle_run_bind]
    have proj : fixedOracleRun o (loopTrace p p.card 0 begin)=Pure.pure st := by
      unfold fixedOracleRun;rw [fixed];rfl
    rw [proj,pure_bind,fixed_oracle_run_bind,body,fixed_oracle_run_pure,pure_bind,fixed_oracle_run_pure,map_pure]
    exact congrArg Pure.pure
      (read_l2b_proof actual l2abi capRaw td p (passEnd o td p) ⟨.success,last,exitCost ((p.card+3)%4)+cycles,0⟩ phys)

end TwoPermutationPrototype.GroupedOpening.Layout2V2
