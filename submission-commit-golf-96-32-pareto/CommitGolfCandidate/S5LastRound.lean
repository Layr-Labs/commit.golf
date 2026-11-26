import CommitGolfCandidate.S5MiddleRounds
import CommitGolfCandidate.S5MaskRun
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
attribute [local irreducible] readBuffer writeBits

theorem last_round (o : Oracle) {d b lane j origin s} (f : ChainFrame o.compression d b lane j origin s)
    (cut : chained d) (last : j+2=calls d) (valid : 2*b+lane.val<count d) :
    ∃ t,Runs .commit true o s t 7 14 1 ∧ PairCtx d b t ∧ t.pc=pcAt (segmentPC d lane+segmentWords d) ∧
      ScratchPad t ∧ NodeEffect o.compression d (2*b+lane.val) origin t := by
  obtain ⟨u,prep,a⟩:=arm_stage o f cut (by omega)
  let idx : Fin 16:=⟨j+1,by have :=(chain_shape d cut).2.1;omega⟩
  obtain ⟨small,_,_,ops⟩:=(chainsites d cut lane).2 idx (by dsimp [idx];omega) (by dsimp [idx];omega)
  have end_ : idx.val+1=calls d:=last
  rw [if_pos end_] at ops
  let p:=2*b+lane.val
  let dst:=dstAddr d p
  let n:=chainStagePC (segmentPC d lane) (j+1)
  let w:=execInstrBr u (.ADDI .x12 .x22 (BitVec.ofNat 12 (toLane lane)))
  let v:=stageReply o.compression d p origin (j+1)
  let raw:=writeBits w (BitVec.ofNat 64 dst) v
  let t:=maskOut raw
  have add : Runs .commit true o u w 1 1 0 := runs_step (decoded_site (by omega) ops.1 u a.pc) rfl
  have ctxw:=ctx_kept a.ctx (show Keeps u w from fun r _ _ x _=>MachineState.getReg_setReg_ne _ _ _ _ x.symm)
  have dest : w.getReg .x12=BitVec.ofNat 64 dst := (chain_addresses a.ctx lane).2.2
  have src : w.getReg .x10=BitVec.ofNat 64 scratchBase:=a.src
  have ip : w.pc=pcAt (n+3) := by change u.pc+4=_;rw [a.pc,pc_succ]
  have data : readBuffer w scratchBase 96=stageInput o.compression d (leftChild origin d p) (rightChild origin d p) (j+1) :=
    (read_congr_mem w u scratchBase 96 rfl).trans a.input
  have bound:=buffers valid
  have hash : Runs .commit true o w raw 1 8 1 := by
    intro fuel
    have law:=hash_fixed .commit true o w fuel scratchBase dst ((decoded_site small ops.2) w ip)
      ctxw.mode ctxw.len ctxw.kind src dest (by decide) (by decide) bound.2.2.1 bound.2.2.2
    rw [data] at law;exact law
  have rawpc : raw.pc=pcAt (maskPC d lane) := by
    rw [show raw.pc=w.pc+4 from reply_pc ..,ip,pc_succ];apply congrArg pcAt;unfold n chainStagePC maskPC;omega
  have ctxraw : PairCtx d b raw:=ctx_kept ctxw (keeps_regs (fun r=>writeBits_register w _ v r))
  have destRaw : raw.getReg .x12=BitVec.ofNat 64 dst := (writeBits_register w _ v _).trans dest
  have projected := mask_run o d lane cut raw dst rawpc destRaw bound.2.2.1 bound.2.2.2
  have finalMem : t.mem=(writeBits w (BitVec.ofNat 64 dst) (storeReply d v)).mem := by
    apply (mask_mem raw dst (heldMask d) destRaw ctxraw.mask).trans
    apply narrow_reply_memory d (chain_shape d cut).2.2.1 (chain_shape d cut).2.2.2.1 w dst v bound.2.2.2
    have :=bound.2.2.1;change dstAddr d p+32≤2^36 at this;change dstAddr d p+32≤2^64;omega
  have frame : unchanged u t dst 32 := by
    intro x k fit apart
    apply (read_congr_mem t _ x k finalMem).trans
    exact ((store_outside w dst _ bound.2.2.1) x k fit apart).trans (read_congr_mem w u x k rfl)
  have dstSmall := parent_below_salts _ _ valid
  have limit : dst+32≤scratchBase :=dstSmall.trans (by decide : rowBase≤scratchBase)
  refine ⟨t,runs_comp (runs_comp (runs_comp prep add) hash) projected,ctx_kept ctxraw (mask_regs raw),?_,?_,⟨?_,?_⟩⟩
  · rw [show t.pc=raw.pc+12 from mask_pc raw,rawpc]
    change pcAt (maskPC d lane)+BitVec.ofNat 64 (4*3)=_
    rw [pc_delta];apply congrArg pcAt;unfold maskPC segmentWords;omega
  · exact pads_after u t a.pads _ _ frame (Or.inr (by omega)) (Or.inr (by omega))
  · apply (read_congr_mem t _ dst 32 finalMem).trans
    apply (written w dst (storeReply d v)).trans
    change storeReply d (o.compression ((parentQueries _ d _ _ (j+1)).getLastD 0))=_
    have nonbottom : d.val≠0 := by unfold chained at cut;omega
    simp only [nodeHash,nonbottom,ite_false,show S5.height d.val=d from Fin.ext (Nat.mod_eq_of_lt d.isLt)]
    unfold parentDigest queries
    rw [show calls d-1=j+1 by omega];rfl
  · intro x k fit apart extra
    exact (frame x k fit apart).trans (a.frame x k fit apart (extra cut).1 (extra cut).2)

theorem chained_lane (o : Oracle) (d : Height) (b : Nat) (lane : Lane) (s : MachineState)
    (cut : chained d) (ctx : PairCtx d b s) (pc : s.pc=pcAt (segmentPC d lane)) (pads : ScratchPad s)
    (g : gaps s) (valid : 2*b+lane.val<count d) :
    ∃ t,Runs .commit true o s t (segmentWords d) (segmentWords d+7*calls d) (calls d) ∧ PairCtx d b t ∧
        t.pc=pcAt (segmentPC d lane+segmentWords d) ∧ ScratchPad t ∧ NodeEffect o.compression d (2*b+lane.val) s t := by
  have lo:=(chain_shape d cut).1
  obtain ⟨a,first,next⟩:=first_round o d b lane s cut ctx pc pads g valid
  obtain ⟨u,mid,armed⟩:=middles o cut (calls d-2) 0 a next (by omega)
  obtain ⟨t,finish,ct,ip,pad,effect⟩:=last_round o armed cut (by omega) valid
  refine ⟨t,?_,ct,ip,pad,effect⟩
  have run:=runs_comp (runs_comp first mid) finish
  unfold segmentWords;convert run using 1 <;> omega
end CommitGolfCandidate.S5Machine
