import CommitGolfCandidate.S5CheckSaltRead
import CommitGolfCandidate.S5CheckLeaf
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def recordLimit (b : Bool) :=if b then 11000 else 3700
def recordQueries (b : Bool) :=if b then 76 else 100
structure RecordResult (o : Oracle) (b : Bool) (x : CheckInput) (r : Nat) (s t : MachineState) (steps : Nat) : Prop where
  run : Flow o s t steps (recordQueries b)
  pc : t.pc=pcAt (rowPC b (pathDepth b))
  value : readBuffer t digestBuf 32=pathValue o.compression b x r (pathDepth b)
  parent : t.getReg .x14=W (positionAt x r (pathDepth b))
  next : RecordRegs b x (r+1) (t.setReg .x23 (W (x.positions.card-(r+1))))
  count : t.getReg .x23=W (x.positions.card-r)
  frame : RecordFrame s t

private theorem row_pre (q : Reg) (h : q∈rowRegs) (q9 : q≠.x9) : q∉([.x6,.x9,.x10,.x14] : List Reg) := by
  cases q <;> simp_all [rowRegs]
private theorem preserved_leaf (q : Reg) (h : q∈rowRegs) (q18 : q≠.x18) : leafLive q:=by cases q <;> simp_all [rowRegs,leafLive]

private theorem record_budget (b : Bool) (ns np f : Nat) (bs : ns≤saltCost b) (budget : np≤pathFuel b 0 (pathDepth b)) (cost : f≤104) :
    3+ns+1+f+np≤recordLimit b := by
  cases b
  · change ns≤7 at bs;change np≤pathFuel false 0 24 at budget;change _≤3700;have lim:=path_limits.1;omega
  · change ns≤438 at bs;change np≤pathFuel true 0 15 at budget;change _≤11000;have lim:=path_limits.2.1;omega
private theorem fifteen : S5.layerBits 15=4030:=by decide +kernel
attribute [local irreducible] readBuffer S5.packedInput S5.bits S5.layerBits
set_option maxRecDepth 10000 in
theorem check_record (o : Oracle) (x : CheckInput) (b : Bool) (r : Nat) (s : MachineState) (lt : r<x.positions.card)
    (mode : b=decide (x.positions.card=BATCH)) (pc : s.pc=pcAt (recordBegin b)) (old : RecordRegs b x r s) :
    ∃ t n,n≤recordLimit b ∧ RecordResult o b x r s t n := by
  let i:=S5.recordIndex x.positions r
  let a:=valueBase+256*r
  have size : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
  change x.positions.card≤16777216 at size
  have room : a+256≤MEMORY_BYTES:=by dsimp [a,valueBase,MEMORY_BYTES];omega
  obtain ⟨u,start,ip,index,next,dest,mem,keep⟩:=record_head o x r b s lt pc old
  have cq:=old.stream.same mem (keep _ (by decide)) (keep _ (by decide)) (keep _ (by decide)) (keep _ (by decide))
  obtain ⟨z,ns,bs,got⟩:=load_salt o x u r b lt mode ip dest cq (old.high.same mem)
  let y:=(z.setReg .x1 (pcAt (saltJump b+1))).setPC (pcAt 62)
  have js:=jump o z (saltJump b) 62 .x1 ((by decide +kernel : ∀ b : Bool,JumpSite (saltJump b) 62 .x1) b) got.pc
  have yk (q : Reg) (neq : q≠.x1) : y.getReg q=z.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ neq.symm)
  have ky (q : Reg) (hq : q∈rowRegs) (ne : q≠.x9) : y.getReg q=s.getReg q:=
    (yk q (by intro eq;subst q;exact (by decide : Reg.x1∉rowRegs) hq)).trans
      ((got.keep q (Or.inl hq)).trans (keep q (row_pre q hq ne)))
  have actualIx : y.getReg .x14=W i.val:=(yk _ (by decide)).trans ((got.keep _ (Or.inr (Or.inr rfl))).trans index)
  have yh : HighInput x y:=((old.high.same mem).after got.mem (by decide)).same rfl
  have data : readBuffer y a 256=S5.recordValue x r:=(yh.read a 256 (by dsimp [a,valueBase,rootBase];omega) room).trans (loaded_value x r lt)
  obtain ⟨w,leaf⟩:=check_leaf o y i a (saltJump b+1) (S5.recordValue x r) ((view b x).salt r) rfl rfl (by cases b <;> decide) actualIx
    data ((read_buffer_memory_congr y z rfl _ _).trans got.data) ((ky _ (by decide) (by decide)).trans old.values)
    ((ky _ (by decide) (by decide)).trans old.leaf) ((ky _ (by decide) (by decide)).trans old.fixed.row)
    ((ky _ (by decide) (by decide)).trans old.fixed.digest) (by dsimp [a,valueBase,leafBuf];omega) room (by dsimp [a,valueBase];omega)
  have wk (q : Reg) (hq : q∈rowRegs) (ne : q≠.x9) (qe : q≠.x18) : w.getReg q=s.getReg q:=
    (leaf.keep q (preserved_leaf q hq qe)).trans (ky q hq ne)
  have cw:=got.cursor.frame (t:=w) (a:=leafBuf) (n:=800) (fun q h al lo=>leaf.frame q h al lo)
    (by decide) (by decide) (by decide)
    ((leaf.keep _ (by simp [leafLive])).trans (yk .x19 (by decide))) ((leaf.keep _ (by simp [leafLive])).trans (yk .x20 (by decide)))
    ((leaf.keep _ (by simp [leafLive])).trans (yk .x21 (by decide))) ((leaf.keep _ (by simp [leafLive])).trans (yk .x22 (by decide)))
  have zero : AtHeight o b x r 0 w := by
    refine ⟨leaf.pc.trans (congrArg pcAt (by cases b <;> rfl)),?_,?_,cw,⟨(wk _ (by decide) (by decide) (by decide)).trans old.fixed.radix,
      (wk _ (by decide) (by decide) (by decide)).trans old.fixed.row,(wk _ (by decide) (by decide) (by decide)).trans old.fixed.chain,
      (wk _ (by decide) (by decide) (by decide)).trans old.fixed.digest⟩,yh.after leaf.frame (by decide)⟩
    · exact (leaf.keep .x14 (by simp [leafLive])).trans (actualIx.trans (congrArg W (by simp [positionAt,S4.nodeIndex,S4.span,i])))
    · apply leaf.output.trans;unfold pathValue S5.Auth.recordAt;rw [S5.Auth.walk,(view_indices x b).1,(view_indices x b).2]
  obtain ⟨t,np,budget,path,result,stable,rowFrame⟩:=path_segment o b x r 0 (pathDepth b) w lt mode (by omega) zero
  have reg (q : Reg) (hq : q∈rowRegs) (a : q≠.x9) (e : q≠.x18) : t.getReg q=s.getReg q:=(stable q hq).trans (wk q hq a e)
  have nextIx : t.getReg .x9=W (indexBase+8*(r+1)):=(stable .x9 (by decide)).trans ((leaf.keep .x9 (by simp [leafLive])).trans
    ((yk _ (by decide)).trans ((got.keep _ (Or.inl (by decide))).trans next)))
  have nextVal : t.getReg .x18=W (valueBase+256*(r+1)):=(stable .x18 (by decide)).trans (leaf.advance.trans (congrArg W (by dsimp [a];omega)))
  let f:=t.setReg .x23 (W (x.positions.card-(r+1)))
  have fk (q : Reg) (ne : q≠.x23) : f.getReg q=t.getReg q:=MachineState.getReg_setReg_ne _ _ _ _ ne.symm
  have finalPc : 0+pathDepth b=pathDepth b:=Nat.zero_add _
  rw [finalPc] at result
  have endBit : peerBit r (pathDepth b)=4030*(r+1) ∨ b=false:=by cases b <;> first | exact Or.inr rfl | (left;change 4030*r+S5.layerBits 15=_;rw [fifteen];omega)
  have endByte : peerOffset r (pathDepth b)=824*(r+1) ∨ b=true:=by cases b <;> first | exact Or.inr rfl | (left;change 824*r+24+32*25=_;omega)
  have nextStream := result.stream.same (t:=f) rfl (fk _ (by decide)) (fk _ (by decide)) (fk _ (by decide)) (fk _ (by decide))
  have stream : WireCursor b x f (4030*(r+1)) (824*(r+1)) := by
    cases b
    · exact nextStream.trans (congrArg (fun pos=>W (proofBase+pos)) (endByte.resolve_right (by decide)))
    · rw [endBit.resolve_right (by decide)] at nextStream;exact nextStream
  have fixed : PathRegs f:=⟨(fk _ (by decide)).trans result.fixed.radix,(fk _ (by decide)).trans result.fixed.row,
    (fk _ (by decide)).trans result.fixed.chain,(fk _ (by decide)).trans result.fixed.digest⟩
  have nextR : RecordRegs b x (r+1) f:=⟨(fk _ (by decide)).trans ((reg _ (by decide) (by decide) (by decide)).trans old.root),
    (fk _ (by decide)).trans nextIx,(fk _ (by decide)).trans nextVal,rfl,(fk _ (by decide)).trans ((reg _ (by decide) (by decide) (by decide)).trans old.leaf),
    fixed,stream,result.inputs.same rfl⟩
  have prior : RecordFrame s y:=(RecordFrame.same mem).trans (RecordFrame.salt got.mem)
  have all:=((((start.trans got.run).trans js).trans leaf.run).trans path)
  have cost : (if i.val.testBit 0 then 103 else 104)≤104:=by split <;> decide
  refine ⟨t,3+ns+1+(if i.val.testBit 0 then 103 else 104)+np,?_,⟨?_,result.pc,result.digest,result.index,nextR,
    (reg _ (by decide) (by decide) (by decide)).trans old.count,(prior.trans (RecordFrame.cache leaf.frame)).trans (RecordFrame.row rowFrame)⟩⟩
  · exact record_budget b ns np _ bs budget cost
  · have calls : 4+pathCalls 0 (pathDepth b)=recordQueries b:=by cases b <;> simp [pathDepth,recordQueries,path_limits.2.2.1,path_limits.2.2.2]
    simpa only [Nat.zero_add,Nat.add_zero,calls,i] using all
end CommitGolfCandidate.S5Machine.Check
