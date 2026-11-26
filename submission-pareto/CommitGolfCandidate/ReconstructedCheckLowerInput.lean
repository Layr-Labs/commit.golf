import CommitGolfCandidate.ReconstructedCheckLowerGeometry
import CommitGolfCandidate.ReconstructedCheckMixed
import CommitGolfCandidate.ReconstructedCheckLowerAdvance
import CommitGolfCandidate.ReconstructedCheckEdge

namespace CommitGolfCandidate.Reconstruction.CheckLowerInput
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CheckStream CheckParentWords
open TwoPermutationPrototype.RV64
set_option maxHeartbeats 1650000
set_option maxRecDepth 20000
abbrev W := BitVec.ofNat 64

def sibling (stream c w digit : Nat) : Binding.Digest :=
  CheckEdge.digest (W (HonestStream.get stream c 64)) (W (HonestStream.get stream (c+64) 64))
    (W (HonestStream.get stream (c+128) 64)) ((W digit <<< (w-192)) ||| W (HonestStream.get stream (c+192) (w-192)))

theorem digWords (x y z t : Word) (i : Fin 4) : digWord (CheckEdge.digest x y z t) i=(![x,y,z,t] : Fin 4→Word) i := by
  fin_cases i
  all_goals first
    | change (t++((z++y)++x)).extractLsb' 0 64=x
    | change (t++((z++y)++x)).extractLsb' 64 64=y
    | change (t++((z++y)++x)).extractLsb' 128 64=z
    | change (t++((z++y)++x)).extractLsb' 192 64=t
  all_goals apply BitVec.eq_of_getLsbD_eq;intro k below
  all_goals simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_append,below,decide_true,Bool.true_and]
  all_goals split_ifs <;> first | rfl | omega | congr 1 <;> omega

def keep : List Reg := [.x1,.x2,.x3,.x4,.x8,.x9,.x11,.x12,.x13,.x14,.x19,.x21,.x22,.x23,.x26]
private theorem kept : ∀ r∈keep,r∈CheckLowerPlan.keep ∧ r∈CheckMixed.frame ∧ r≠.x15 ∧ r≠.x24 := by decide

structure In (s : MachineState) (g : Reader) (r : Fin 64) (i : Fin 15) (cell : Nat) : Prop where
  pc : s.pc=CommitBlocks.addr 280
  cursor : s.getReg .x24=W (64*g.block+r.val)
  proof : s.getReg .x19=W g.proofBase
  widthCell : s.getReg .x9=W g.widthCell
  fp : s.getReg .x8=W (g.maskCell+2368)
  width : s.getMem (W g.widthCell)=W (CheckMixed.width i)
  mask : s.getMem (W g.maskCell)=0xffffffff
  depth : s.getReg .x26=W (10+i.val)
  divisor : s.getReg .x22=wordAddress cell
  base : s.getMem (wordAddress cell)=W (CheckMixed.base i)

theorem positive (o : Oracle) (s : MachineState) (g : Reader) (r : Fin 64) (i : Fin 15) (cell stream : Nat)
    (placed : CheckLowerGeometry.Placed g) (source : Source s g stream) (room : cell<2^33) (call : In s g r i cell)
    (q3 q2 q1 q0 : Fin (2^32)) (hdr : CheckMixed.typed s q3 q2 q1 q0) :
    let c:=64*g.block+r.val
    let w:=CheckMixed.width i
    let v:=CheckMixed.out i [q3.val,q2.val,q1.val,q0.val]
    ∃ t n,n≤103 ∧ Segment o n s t [] ∧ t.pc=CommitBlocks.addr 248 ∧ CheckRecordHeader.limbs t=v.1 ∧
      CheckPairPhysical.child t CheckPair.sibling (sibling stream c w v.2) ∧
      t.getReg .x24=W (c+w) ∧ t.getReg .x15=(s.getReg .x23 &&& 1) ∧
      (∀ r∈keep,t.getReg r=s.getReg r) ∧ (∀ a,a<2^33→t.getMem (wordAddress a)=s.getMem (wordAddress a)) := by
  let c:=64*g.block+r.val
  let w:=CheckMixed.width i
  let v:=CheckMixed.out i [q3.val,q2.val,q1.val,q0.val]
  obtain ⟨u,read,pos,low,middle,high,top,extra,width,cursor,mem,guardVal,sub,preserve,_⟩:=
    CheckLowerGeometry.read o s g placed r i stream source call.pc call.cursor call.proof call.widthCell call.fp call.width call.mask
  have head : CheckMixed.typed u q3 q2 q1 q0 := by
    obtain ⟨h3,h2,h1,h0⟩:=hdr
    exact ⟨(preserve .x27 (by decide)).trans h3,(preserve .x18 (by decide)).trans h2,
      (preserve .x20 (by decide)).trans h1,(preserve .x25 (by decide)).trans h0⟩
  have x28 : u.getReg .x28=W (10+i.val)+(-8) := sub.trans (congrArg (·+(-8)) call.depth)
  obtain ⟨y,m,small,division,loc,quots,joined,retained,clean⟩:=CheckMixed.positive o u i cell room pos guardVal x28
    ((preserve .x22 (by decide)).trans call.divisor) ((mem _).trans call.base) width q3 q2 q1 q0 head
  obtain ⟨t,advance,ready,bits,parity,regs,frame⟩:=CheckLowerAdvance.positive o y loc
  have path:=compose (compose read division) advance
  have bounded : (CheckLowerPlan.done r w).ticks≤70:=by
    have h:=CheckLowerPlan.checked r i;simp only [CheckLowerPlan.receipt,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1.2.2.2.2.2.2.2.2.2
  have pass (reg : Reg) (hk : reg∈keep) : t.getReg reg=s.getReg reg := by
    obtain ⟨first,second,n15,n24⟩:=kept reg hk
    exact (regs reg n15 n24).trans ((retained reg second).trans (preserve reg first))
  have val (a : Word) (b : Nat) (h : a.toNat=b) : a=W b:=by rw [←h];simp [W]
  refine ⟨t,(CheckLowerPlan.done r w).ticks+m+2,by omega,by simpa only [w,CheckMixed.width,List.nil_append] using path,ready,?_,?_,?_,?_,pass,?_⟩
  · change [_,_,_,_]=_
    simp only [CheckRecordHeader.limbs] at quots
    rw [regs .x27 (by decide) (by decide),regs .x18 (by decide) (by decide),regs .x20 (by decide) (by decide),regs .x25 (by decide) (by decide)]
    exact quots
  · intro j;unfold sibling
    rw [digWords];fin_cases j
    · change t.getReg .x10=_;rw [regs .x10 (by decide) (by decide),retained .x10 (by decide)];exact val _ _ low
    · change t.getReg .x16=_;rw [regs .x16 (by decide) (by decide),retained .x16 (by decide)];exact val _ _ middle
    · change t.getReg .x17=_;rw [regs .x17 (by decide) (by decide),retained .x17 (by decide)];exact val _ _ high
    · change t.getReg .x6=_;rw [regs .x6 (by decide) (by decide),joined,val _ _ top];rfl
  · change t.getReg .x24=W (c+w)
    rw [bits,retained .x5 (by decide),retained .x24 (by decide),extra,cursor,←BitVec.ofNat_add]
    congr 1
    have widthBound : 192≤w:=(by decide : ∀ j : Fin 15,192≤CheckMixed.width j) i
    change (w-192)+(c+192)=c+w;omega
  · rw [parity,retained .x23 (by decide),preserve .x23 (by decide)]
  · intro a ha;exact (frame _).trans ((clean a ha).trans (mem _))

end CommitGolfCandidate.Reconstruction.CheckLowerInput
