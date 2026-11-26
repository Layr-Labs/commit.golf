import CommitGolfCandidate.ReconstructedCheckLowerInput
import CommitGolfCandidate.ReconstructedCheckLowerReturn

namespace CommitGolfCandidate.Reconstruction.CheckLowerRound
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CheckParentGeometry CheckPairPhysical
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1950000
abbrev W:=BitVec.ofNat 64

def depth (i : Fin 15) : Fin 24 := ⟨9+i.val,by have:=i.isLt;omega⟩

def entered (s : MachineState) (geo : Geometry) (i : Fin 15) (side : Bool) :=
  s.getReg .x2=W (geo.stack+144) ∧ s.getReg .x8=W (geo.pair+2360) ∧
  s.getReg .x21=W (depth i) ∧ (s.getReg .x23 &&& 1)=(if side then 1 else 0)

def Outside (geo : Geometry) (p : Word) := (∀ i : Fin 8, p≠W (geo.pair+8*i.val)) ∧
    (∀ i : Fin 18,p≠W (geo.stack+8*i.val)) ∧ (∀ i : Fin 4,p≠W (geo.out+8*i.val))

private theorem positiveBase : ∀ i : Fin 15, 0<CheckMixed.base i ∧ CheckMixed.base i≤2^31 ∧
    Binding.radix ((depth i).val+1)=CheckMixed.base i*2^(CheckMixed.width i-192) := by decide

private theorem narrow (i : Fin 15) (q3 q2 q1 q0 : Fin (2^32)) :
    (CheckMixed.out i [q3.val,q2.val,q1.val,q0.val]).2<CheckMixed.base i := by
  have b:=positiveBase i
  unfold CheckMixed.out;split
  · have h:=(HonestDivision.four_limbs (CheckMixed.base i) q3 q2 q1 q0 b.1 (Nat.le_trans b.2.1 (by decide))).2
    rw [h];exact Nat.mod_lt _ b.1
  · exact b.1

theorem canonical (stream c : Nat) (i : Fin 15) (z : Nat) (small : z<CheckMixed.base i) :
    Canonical ((depth i).val+1) (CheckLowerInput.sibling stream c (CheckMixed.width i) z) := by
  apply CheckEdge.projected (b:=CheckMixed.base i)
  · exact (positiveBase i).2.2
  · change (HonestStream.get stream (c+192) (CheckMixed.width i-192))%2^64<_
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
  · change z%2^64<_;exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) small

structure Return (s t : MachineState) (i : Fin 15) (nextCursor : Nat) (xs : List Nat) : Prop where
  pc : t.pc=CommitBlocks.addr (if (depth i).val≤9 then 381 else 280)
  sp : t.getReg .x2=s.getReg .x2
  fp : t.getReg .x8=s.getReg .x8
  header : CheckRecordHeader.limbs t=xs
  route : t.getReg .x23=s.getReg .x23 >>> (1 : Nat)
  bit : t.getReg .x24=W nextCursor
  source : t.getReg .x19=s.getReg .x19
  widthPtr : t.getReg .x9=s.getReg .x9+(-8)
  basePtr : t.getReg .x22=s.getReg .x22+(-8)
  parentDepth : t.getReg .x21=((s.getReg .x21).truncate 32+((-1#64).truncate 32)).signExtend 64
  childDepth : t.getReg .x26=s.getReg .x26+(-1)

/-- One full lower Merkle traversal step, from bit input to the recorded parent. -/
theorem positive (o : Oracle) (s : MachineState) (g : CheckStream.Reader) (r : Fin 64) (i : Fin 15)
    (cell stream : Nat) (placed : CheckLowerGeometry.Placed g) (source : CheckStream.Source s g stream)
    (room : cell<2^33) (input : CheckLowerInput.In s g r i cell) (q3 q2 q1 q0 : Fin (2^32))
    (head : CheckMixed.typed s q3 q2 q1 q0) (geo : Geometry) (areas : Placed geo) (anchor : geo.pair+2048=geo.out)
    (ro : constants s) (side : Bool) (entry : entered s geo i side) (cur : Binding.Digest)
    (childOk : Canonical ((depth i).val+1) cur) (current : child s CheckPair.current cur) :
    let c:=64*g.block+r.val
    let w:=CheckMixed.width i
    let hdr:=CheckMixed.out i [q3.val,q2.val,q1.val,q0.val]
    let sib:=CheckLowerInput.sibling stream c w hdr.2
    let pars:=sides side cur sib
    let par:=parent (oracleCompression o) (depth i) pars.1 pars.2
    let rows:=log o (depth i) side cur sib
    ∃ t n, n≤305 ∧ Segment o n s t rows ∧ Return s t i (c+w) hdr.1 ∧ child t CheckPair.current par ∧
      Nonempty (CheckPath.Edge o rows (depth i) side cur par) ∧
      (∀ a,a<2^33→Outside geo (wordAddress a)→t.getMem (wordAddress a)=s.getMem (wordAddress a)) := by
  let c:=64*g.block+r.val
  let w:=CheckMixed.width i
  let hdr:=CheckMixed.out i [q3.val,q2.val,q1.val,q0.val]
  let sib:=CheckLowerInput.sibling stream c w hdr.2
  let d:=depth i
  obtain ⟨u,n,small,read,pc,limbs,sibling,cursor,parity,regs,frame⟩:=CheckLowerInput.positive o s g r i cell stream placed source room input q3 q2 q1 q0 head
  obtain ⟨sp,fp,depthReg,branch⟩:=entry
  have called : CheckPairPhysical.Called u geo d side:=⟨pc,(regs .x8 (by decide)).trans fp,(regs .x2 (by decide)).trans sp,
    parity.trans branch,(regs .x21 (by decide)).trans depthReg,anchor⟩
  have curU : child u CheckPair.current cur:=by intro j;exact (regs _ ((by decide : ∀ k : Fin 4,CheckPair.current k∈CheckLowerInput.keep) j)).trans (current j)
  have roU : constants u:=by
    intro a v aligned known
    have smallA : a<2^36:=by unfold CheckParentRun.ro at known;split_ifs at known <;> first | contradiction | omega
    have addr : wordAddress (a/8)=W a:=by unfold wordAddress;congr 1;omega
    change u.getMem (W a)=v
    rw [←addr,frame _ (by omega),addr];exact ro _ _ aligned known
  obtain ⟨v,hash,vpc,computed,heap,fpV,memV,spV,dec,passed⟩:=CheckPairPhysical.complete o u geo areas d side called roU cur sib curU sibling
  have d26 : v.getReg .x26=W d:=by
    rw [dec,regs .x26 (by decide),input.depth]
    exact (by decide : ∀ j : Fin 15,W (10+j.val)+(-1)=W (depth j)) i
  have fpOut : v.getReg .x8=W (geo.out+312):=by rw [fpV,called.fp,←anchor]
  obtain ⟨t,finish,tpc,parentWords,keepT,memT,wPtr,bPtr,step⟩:=CheckLowerReturn.positive o v geo.out d vpc fpOut d26 (areas.align 3) (areas.room 3)
  have sibOk : Canonical (d.val+1) sib:=canonical stream c i _ (narrow i q3 q2 q1 q0)
  have limit : CheckParent.Cost d≤170:= (CheckParentPlan.checked d).2
  let rs:=log o d side cur sib
  refine ⟨t,n+(23+CheckParent.Cost d)+9,by omega,by simpa only [List.nil_append,List.append_nil] using compose (compose read hash) finish,?_,?_,?_,?_⟩
  · refine ⟨tpc,(keepT .x2 (by decide)).trans (spV.trans (regs .x2 (by decide))),
      (keepT .x8 (by decide)).trans (fpV.trans (regs .x8 (by decide))),?_,?_,?_,?_,?_,?_,?_,?_⟩
    · unfold CheckRecordHeader.limbs at limbs ⊢
      rw [keepT .x27 (by decide),keepT .x18 (by decide),keepT .x20 (by decide),keepT .x25 (by decide),
        passed .x27 (by decide),passed .x18 (by decide),passed .x20 (by decide),passed .x25 (by decide)];exact limbs
    · rw [keepT .x23 (by decide),heap,regs .x23 (by decide)]
    · rw [keepT .x24 (by decide),passed .x24 (by decide)];exact cursor
    · rw [keepT .x19 (by decide),passed .x19 (by decide),regs .x19 (by decide)]
    · rw [wPtr,passed .x9 (by decide),regs .x9 (by decide)]
    · rw [bPtr,passed .x22 (by decide),regs .x22 (by decide)]
    · rw [step,passed .x21 (by decide),regs .x21 (by decide)]
    · rw [keepT .x26 (by decide),dec,regs .x26 (by decide)]
  · rw [computed] at parentWords;exact parentWords
  · refine ⟨(sides side cur sib).1,(sides side cur sib).2,?_,?_,?_,rfl,fun _ h=>h⟩
    · cases side <;> assumption
    · cases side <;> assumption
    · cases side <;> rfl
  · intro a bounded away;exact (memT _).trans ((memV _ away.1 away.2.1 away.2.2).trans (frame a bounded))

end CommitGolfCandidate.Reconstruction.CheckLowerRound
