import CommitGolfCandidate.R4ParentHash
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ rowAddress nodeAddress)
attribute [local irreducible] DetRun writeBits readBuffer
set_option maxRecDepth 5000 in
theorem laneRun (o : Oracle) (s : MachineState) (n p : Nat) (d : Width)
    (hi : p<nodes d) (f : Pointers d p s) (pc : s.pc=pcAt n) (code : LaneCode n (extra d) (destInc p)) :
    ∃ t,MRun o s (laneWidth d) t (laneWidth d+7) 1 ∧ t.pc=pcAt (n+laneWidth d) ∧
      Pointers d (p+1) t ∧ t.getReg .x19=s.getReg .x19 ∧
      t.mem=(Late.writeParent (Late.layerHash o.compression d) s d p).mem := by
  let a:=nodeAddress (d.val+1) p
  let b:=rowAddress d p
  let w:=o.compression (readBuffer s b 96)
  let raw:=writeBits s (Z a) w
  obtain ⟨v,m,call⟩:=callAndMask o s n p d hi f pc code
  let u:=execInstrBr v (.ADDI .x10 .x10 96)
  let t:=execInstrBr u (.ADDI .x12 .x12 (BitVec.ofNat 12 (destInc p)))
  have step : MRun o v 1 u 1 0:=DetRun.step1 (code.nextSrc _ m.pc) rfl
  have pcu : u.pc=pcAt (n+1+extra d+1):=(congrArg (·+4) m.pc).trans (pc_succ _).symm
  have last : MRun o u 1 t 1 0:=DetRun.step1 (code.nextDst _ pcu) rfl
  have keep (r : Reg) (a : r≠.x10) (b : r≠.x12) (c : r≠.x6) : t.getReg r=s.getReg r:=
    (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ b.symm)).trans
      ((MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ a.symm)).trans (m.keep r c))
  have inc : destInc p<2048:=by unfold destInc;split <;> decide
  have dx : t.getReg .x12=Z (nodeAddress (d.val+1) (p+1)):=by
    change u.getReg .x12+signExtend12 _=_
    rw [show u.getReg .x12=v.getReg .x12 from rfl,m.keep _ (by decide),f.dst,add_signExtend12_ofNat_small _ _ inc,addrDst]
  have sx : t.getReg .x10=Z (rowAddress d (p+1)):=by
    change v.getReg .x10+signExtend12 96=_
    rw [m.keep _ (by decide),f.src];exact (add_signExtend12_ofNat_small _ 96 (by decide)).trans (congrArg Z (addrSrc d p))
  have data : t.mem=(writeBits s (Z a) (Late.retain (23-d.val) w)).mem:=m.mem
  have heq : 24-(23-d.val)=d.val+1:=by have:=d.isLt;omega
  refine ⟨t,?_,?_,⟨⟨(keep _ (by decide) (by decide) (by decide)).trans f.mode,(keep _ (by decide) (by decide) (by decide)).trans f.kind,
    (keep _ (by decide) (by decide) (by decide)).trans f.width,(keep _ (by decide) (by decide) (by decide)).trans f.root⟩,sx,dx,
    (keep _ (by decide) (by decide) (by decide)).trans f.mask⟩,keep _ (by decide) (by decide) (by decide),?_⟩
  · have path : MRun o s (1+extra d+1+1) t (8+extra d+1+1) 1:=((call.trans m.run).trans step).trans last
    rwa [show 1+extra d+1+1=laneWidth d by unfold laneWidth;omega,show 8+extra d+1+1=laneWidth d+7 by unfold laneWidth;omega] at path
  · apply (congrArg (·+4) pcu).trans
    rw [←pc_succ];apply congrArg pcAt;unfold laneWidth;omega
  · unfold Late.retain at data;rw [heq] at data;exact data

end CommitGolfCandidate.R4
