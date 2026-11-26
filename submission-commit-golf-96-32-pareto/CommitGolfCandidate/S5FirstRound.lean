import CommitGolfCandidate.S5ChainCommon
import CommitGolfCandidate.Stage3cCompletedParent
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
private theorem dest_reply (s : MachineState) (src dst : Reg) (a b : BitVec 12) (w : Output) :
    (callState s src dst a b w).getReg .x12=(prepareCall s src dst a b).getReg .x12 :=
  writeBits_register (prepareCall s src dst a b) _ w .x12
attribute [local irreducible] readBuffer writeBits callState stageInput

def leftChild (s : MachineState) (d : Height) (p : Nat) := readBuffer s (srcAddr d p) 32
def rightChild (s : MachineState) (d : Height) (p : Nat) :=readBuffer s (srcAddr d p+32) 32
def stageReply (H : Compression) (d : Height) (p : Nat) (s : MachineState) (j : Nat) :=
  H (stageInput H d (leftChild s d p) (rightChild s d p) j)

structure ChainFrame (H : Compression) (d : Height) (b : Nat) (lane : Lane) (j : Nat) (origin s : MachineState) : Prop where
  ctx : PairCtx d b s
  pc : s.pc=pcAt (chainStagePC (segmentPC d lane) (j+1))
  src : s.getReg .x10=BitVec.ofNat 64 scratchBase
  dest : s.getReg .x12=BitVec.ofNat 64 scratchBase
  value : readBuffer s scratchBase 32=stageReply H d (2*b+lane.val) origin j
  pads : ScratchPad s
  frame : outsideLane d (2*b+lane.val) origin s

theorem pc_delta (a n : Nat) : pcAt a+BitVec.ofNat 64 (4*n)=pcAt (a+n) := by
  unfold pcAt;rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega

theorem first_round (o : Oracle) (d : Height) (b : Nat) (lane : Lane) (s : MachineState)
    (cut : chained d) (ctx : PairCtx d b s) (pc : s.pc=pcAt (segmentPC d lane)) (pads : ScratchPad s)
    (g : gaps s) (valid : 2*b+lane.val<count d) :
    ∃ t,Runs .commit true o s t 5 12 1 ∧ ChainFrame o.compression d b lane 0 s t := by
  let p:=2*b+lane.val
  let n:=segmentPC d lane
  let from_:=BitVec.ofNat 12 (fromLane lane)
  let a:=srcAddr d p
  let tag:=tagWord d 0
  let s₁:=(tagStore s a tag).setPC (s.pc+4)
  let answer:=stageReply o.compression d p s 0
  let s₄:=callState s₁ .x21 .x24 from_ 0 answer
  let t:=execInstrBr s₄ (.ADDI .x10 .x24 0)
  obtain ⟨limit,w0,w1,w2,w3,w4⟩:=(chainsites d cut lane).1
  obtain ⟨src,destTag,dst⟩:=chain_addresses ctx lane
  have bounds:=buffers valid
  have aFit : a+96≤MEMORY_BYTES:=bounds.1
  have aAl : a%8=0:=bounds.2.1
  have gFit:=gap_limit d p valid
  have head : Runs .commit true o s s₁ 1 1 0 := by
    apply runs_pure;intro fuel
    have law:=sd_run (pg:=.commit) fuel true ((decoded_site (by omega) w0) s pc) (tagAddr d p) destTag
      (by change _≤2^36;unfold rowBase at gFit;omega) (by change (a+64)%8=0;omega)
    rw [ctx.tag] at law;exact law
  have keep1 : Keeps s s₁:=keeps_regs fun _=>rfl
  have ctx₁:=ctx_kept ctx keep1
  have here : s₁.pc=pcAt (n+1) := by change s.pc+4=_;rw [pc,pc_succ]
  have out : readBuffer s₁ a 96=stageInput o.compression d (leftChild s d p) (rightChild s d p) 0 := by
    unfold stageInput
    exact (read_congr_mem s₁ (tagStore s a tag) a 96 rfl).trans (first_tag_value g a rfl cut valid)
  have addresses:=call_addresses s₁ .x21 .x24 from_ 0 (by decide)
  have xs : (prepareCall s₁ .x21 .x24 from_ 0).getReg .x10=BitVec.ofNat 64 a :=
    addresses.1.trans (chain_addresses ctx₁ lane).1
  have ys : (prepareCall s₁ .x21 .x24 from_ 0).getReg .x12=BitVec.ofNat 64 scratchBase := by rw [addresses.2,ctx₁.scratch];rfl
  have run:=three_calls o s₁ (n+1) .x21 .x24 from_ 0 a scratchBase (decoded_site (by omega) w1)
    (decoded_site (by omega) w2) (decoded_site (by omega) w3) here ctx₁.toCommon xs ys aFit aAl (by decide) (by decide)
  rw [out] at run
  have run₃ : Runs .commit true o s₁ s₄ 3 10 1:=run
  have ip : s₄.pc=pcAt (n+4) := by rw [show s₄.pc=s₁.pc+12 from call_pc ..,here];exact pc_delta (n+1) 3
  have set:=runs_step (coins:=true) (o:=o) (decoded_site limit w4 s₄ ip) (show ordinaryStep s₄ (.base (.ADDI .x10 .x24 0))=some t from rfl)
  have keep₄ : Keeps s₁ s₄:=fun r _ x y _=>call_register _ _ _ r _ _ _ x.symm y.symm
  have ctx₄:=ctx_kept ctx₁ keep₄
  have keepT : Keeps s₄ t := fun r _ x _ _=>MachineState.getReg_setReg_ne _ _ _ _ x.symm
  have mem₄ : s₄.mem=(writeBits s₁ (BitVec.ofNat 64 scratchBase) answer).mem := by
    apply (call_memory s₁ .x21 .x24 from_ 0 answer (by decide)).trans
    exact congrArg (fun addr=>(writeBits s₁ addr answer).mem) (addresses.2.symm.trans ys)
  have tagFrame : unchanged s s₁ (tagAddr d p) 8 := by
    intro x k fit apart;exact (read_congr_mem s₁ (tagStore s a tag) x k rfl).trans (tag_outside s a tag aAl aFit x k fit apart)
  have storeFrame : unchanged s₁ t scratchBase 32 := by
    intro x k fit apart;exact (read_congr_mem t _ x k mem₄).trans (store_outside s₁ scratchBase answer (by decide) x k fit apart)
  have av : tagAddr d p+8≤scratchBase:=by unfold scratchBase rowBase at *;omega
  have retained : ScratchPad s₁ := pads_after s s₁ pads _ _ tagFrame (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨t,runs_comp (runs_comp head run₃) set,⟨ctx_kept ctx₄ keepT,?_,?_,?_,?_,?_,?_⟩⟩
  · change s₄.pc+4=pcAt _;rw [ip,pc_succ];rfl
  · change s₄.getReg .x24+signExtend12 0=_;rw [ctx₄.scratch];rfl
  · change s₄.getReg .x12=_
    exact (dest_reply s₁ .x21 .x24 from_ 0 answer).trans ys
  · exact (read_congr_mem t _ scratchBase 32 mem₄).trans (written s₁ scratchBase answer)
  · exact pads_after _ _ retained _ _ storeFrame (Or.inr (by omega)) (Or.inr (by omega))
  · apply outside_trans (outside_footprint tagFrame (fun _ _ _ tag _=>tag))
    exact outside_footprint storeFrame (by intro x k _ _ cover;rcases cover with left|right <;> unfold Apart <;>omega)
end CommitGolfCandidate.S5Machine
