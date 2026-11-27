import CommitGolfCandidate.Stage3cCheckLeafSalt
import CommitGolfCandidate.Stage3cCheckLeafCalls
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
private def setupLeaf : List Sym.Calc := [.addi .x5 .x0 0,.addi .x11 .x0 96,.addi .x13 .x0 0]
private theorem setup_leaf (o : Oracle) (s : MachineState) (odd : Bool) (pc : s.pc=pcAt 157)
    (l : s.getReg .x24=W leafBuf) (r : s.getReg .x25=W rowBuf) (d : s.getReg .x27=W digestBuf)
    (slot : s.getReg .x29=W (rowBuf+laneOffset odd)) :
    ∃ t,Flow o s t 3 0 ∧ t.pc=pcAt 160 ∧ t.mem=s.mem ∧ LeafSys t odd ∧
      ∀ q,q∉([.x5,.x11,.x13] : List Reg) → t.getReg q=s.getReg q := by
  obtain ⟨run,reg,mem,ep⟩:=Sym.compiled o setupLeaf 157 s pc (by decide +kernel)
    (by change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  have keep (q : Reg) (h : q∉([.x5,.x11,.x13] : List Reg)) : (Sym.evaluated setupLeaf s).getReg q=s.getReg q:=by
    apply (reg q).trans;cases q <;> first | rfl | (exfalso;apply h;decide)
  exact ⟨_,run,ep,mem,⟨(keep _ (by decide)).trans l,(keep _ (by decide)).trans r,(keep _ (by decide)).trans d,
    (keep _ (by decide)).trans slot,reg .x5,reg .x13,reg .x11⟩,keep⟩

private theorem leaf_ret (o : Oracle) (s : MachineState) (back : Nat) (limit : back<2147)
    (pc : s.pc=pcAt 172) (ra : s.getReg .x1=pcAt back) : Flow o s (s.setPC (pcAt back)) 1 0 := by
  apply one_flow o pc (known (by decide +kernel)) (i:=.JALR .x0 .x1 0)
  change some (s.setPC ((s.getReg .x1+signExtend12 0) &&& ~~~1#64))=_
  rw [ra,show signExtend12 0=0#64 by rfl,BitVec.add_zero,(by decide +kernel : ∀ j : Fin 2147,pcAt j.val &&& ~~~1#64=pcAt j.val) ⟨back,limit⟩]

structure LeafResult (o : Oracle) (s t : MachineState) (back a : Nat) (i : Index) (v : Entry) (salt : Late.Salt) : Prop where
  run : Flow o s t (if i.val.testBit 0 then 103 else 104) 4
  pc : t.pc=pcAt back
  output : readBuffer t digestBuf 32=Late.leaf o.compression (i.val.testBit 0) salt v
  advance : t.getReg .x18=W (a+256)
  keep : LeafPreserves s t
  frame : Outside s t leafBuf 800

private theorem live_subset (q : Reg) (h : leafLive q) : q∉([.x6,.x7,.x28,.x29] : List Reg) ∧
    q∉([.x5,.x11,.x13] : List Reg) ∧ q≠.x10 ∧ q≠.x12 := by cases q <;> simp_all [leafLive]
attribute [local irreducible] readBuffer leafEffect
set_option maxRecDepth 10000 in
theorem check_leaf (o : Oracle) (s : MachineState) (i : Index) (a back : Nat) (value : Entry) (salt : Late.Salt)
    (pc : s.pc=pcAt 62) (ra : s.getReg .x1=pcAt back) (limit : back<2147) (idx : s.getReg .x14=W i.val)
    (msg : readBuffer s a 256=value) (random : readBuffer s saltBuf 24=salt) (sp : s.getReg .x18=W a)
    (leaf : s.getReg .x24=W leafBuf) (row : s.getReg .x25=W rowBuf) (dg : s.getReg .x27=W digestBuf)
    (low : leafBuf+256≤a) (room : a+256≤MEMORY_BYTES) (al : a%8=0) : ∃ t,LeafResult o s t back a i value salt := by
  let odd:=i.val.testBit 0
  obtain ⟨u,start⟩:=leaf_prefix o s a value salt pc msg random sp leaf row low room al
  obtain ⟨v,pack,pcv,slot,saved,pad,frame,keep⟩:=leaf_salt o u i.val salt start.pc ((start.keep _ (by simp [leafLive])).trans idx)
    ((start.keep _ (by simp [leafLive])).trans row) start.salt start.zeros
  have vr (q : Reg) (h : leafLive q) : v.getReg q=s.getReg q:=(keep q (live_subset q h).1).trans (start.keep q h)
  obtain ⟨z,setup,ip,mem,sys,zk⟩:=setup_leaf o v odd pcv ((vr _ (by simp [leafLive])).trans leaf)
    ((vr _ (by simp [leafLive])).trans row) ((vr _ (by simp [leafLive])).trans dg) slot
  obtain ⟨w,hashes,ipw,wk,finalMem⟩:=four_leaf_calls o z odd ip sys
  have reg (q : Reg) (h : leafLive q) : w.getReg q=s.getReg q:=by
    obtain ⟨_,ok,a,b⟩:=live_subset q h;exact (wk q a b).trans ((zk q ok).trans (vr q h))
  have ret:=leaf_ret o w back limit ipw ((reg _ (by simp [leafLive])).trans ra)
  let t:=w.setPC (pcAt back)
  have vb : readBuffer v leafBuf 256=value:=by
    apply (Open.outside_read frame (by cases i.val.testBit 0 <;> decide) (by decide) _ _ (by decide)
      (Or.inl (by cases i.val.testBit 0 <;> decide))).trans start.value
  have data:=leaf_value o.compression z odd value salt ((read_buffer_memory_congr z v mem _ _).trans vb)
    ((read_buffer_memory_congr z v mem _ _).trans pad) ((read_buffer_memory_congr z v mem _ _).trans saved)
  have wframe:=leaf_frame o.compression z odd
  have all:=(((start.run.trans pack).trans setup).trans hashes).trans ret
  refine ⟨t,⟨?_,rfl,(read_buffer_memory_congr t (leafEffect o.compression z odd) finalMem _ _).trans data,?_,
    fun q h=>MachineState.getReg_setPC.trans (reg q h),?_⟩⟩
  · generalize i.val.testBit 0=b at all ⊢;cases b <;> exact all
  · exact MachineState.getReg_setPC.trans ((wk _ (by decide) (by decide)).trans ((zk _ (by decide)).trans ((keep _ (by decide)).trans start.advance)))
  · intro q h aq out
    have sep : q<rowBuf+saltOffset (i.val.testBit 0) ∨ rowBuf+saltOffset (i.val.testBit 0)+24≤q := by
      cases i.val.testBit 0 <;> unfold leafBuf at out <;> change _ ∨ _≤_ <;> dsimp [rowBuf,saltOffset] <;> omega
    have smallOut : q<leafBuf ∨ leafBuf+352≤q:=by omega
    have f1:=start.frame q h aq smallOut
    have f2:=frame q h aq sep
    have f3:=congrFun mem (W q)
    have f4:=wframe q h aq out
    exact (congrFun finalMem (W q)).trans (f4.trans (f3.trans (f2.trans f1)))
end CommitGolfCandidate.Chained.BinaryMachine.Check
