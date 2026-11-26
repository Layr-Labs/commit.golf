import CommitGolfCandidate.ReconstructedOpeningSaltHigh
import CommitGolfCandidate.ReconstructedOpeningRead

namespace CommitGolfCandidate.Reconstruction.OpeningRecordSalt
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery Generator
open TwoPermutationPrototype.RV64 OpeningPut OpeningCursor OpeningReply LeafContent
open TwoPermutationPrototype (writeWord writeWindow)
open CommitBlocks (addr)
open CommitWindows (generatorBase)
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] ArtifactEncoding.decode execute

def answer (o : Oracle) (m : Model) (ord : Nat) (i : Index) :=
  (atQuery m ord).permute o (start i) replyBase

theorem kept (o : Oracle) (m : Model) (ord : Nat) (i : Index) :
    let t := answer o m ord i
    t.reg .x0=m.reg .x0 ∧ t.reg .x6=m.reg .x6 ∧ t.reg .x7=m.reg .x7 ∧
    t.reg .x8=m.reg .x8 ∧ t.reg .x22=m.reg .x22 ∧ t.reg .x25=m.reg .x25 ∧ t.reg .x31=m.reg .x31 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem stackPointer (o : Oracle) (m : Model) (ord : Nat) (i : Index) :
    (answer o m ord i).reg .x2=m.reg .x2 := rfl

attribute [local irreducible] atQuery

theorem preserved_output (o : Oracle) (m : Model) (ord : Nat) (i : Index) (ent : Entry m ord i) (j : Nat)
    (bound : j<capacity) : (answer o m ord i).mem (base+j)=m.mem (base+j) := by
  have h := (setup o m ord i ent).2.2
  have jlo : generatorBase+1 ≠ base+j := by unfold generatorBase base;omega
  have hi : base+j<savePtr := by unfold base savePtr capacity at *;omega
  have oth : base+j ≠ saveCount := by unfold base saveCount capacity at *;omega
  have high : ¬(replyBase≤base+j ∧ base+j<replyBase+25) := by unfold replyBase base capacity at *;omega
  simp only [answer,Model.permute,writeWindow,high,dite_false,h,saves,Model.store,
    writeWord,Ne.symm jlo,ne_of_lt hi,oth,ite_false]

def saltFields (o : Oracle) (k : Key) (i : Index) : List Wire.Field :=
  let reply := tapeReply o k i
  let lane := laneOf i
  [⟨(replyWords reply (LeafNonce.firstWord lane)).toNat,64⟩,
   ⟨(replyWords reply (LeafNonce.nextWord lane)).toNat,56⟩]

theorem fits_after_low (c : Nat) (room : (c+64)/64<capacity) (l : Fin 12) (m : TwoPermutationPrototype.Memory) (v : Word) :
    (put m c 64 v) (replyBase+(LeafNonce.nextWord l).val)=m (replyBase+(LeafNonce.nextWord l).val) := by
  apply OpeningPut.keep
  all_goals have b := (LeafNonce.nextWord l).isLt;unfold replyBase cell base capacity at *;omega

def steps (c : Nat) (i : Index) :=
  42+(6+(if (laneOf i).val=0 then 3 else 4)+4)+(4+(if c%64=0 then 1 else 8)+1)+11+
    OpeningSaltHigh.steps (c+64)

structure Result (o : Oracle) (m t : Model) (k : Key) (ord c : Nat) (i : Index) : Prop where
  memory : t.mem=put (put (answer o m ord i).mem c 64 (replyWords (tapeReply o k i) (LeafNonce.firstWord (laneOf i))))
    (c+64) 56 (OpeningSaltHigh.clip (replyWords (tapeReply o k i) (LeafNonce.nextWord (laneOf i))))
  position : t.reg .x15=BitVec.ofNat 64 i.val
  cursor : t.reg .x7=W c
  frame : t.reg .x8=m.reg .x8
  tree : t.reg .x22=m.reg .x22
  proofBase : t.reg .x25=m.reg .x25
  zero : t.reg .x0=m.reg .x0
  sp : t.reg .x2=m.reg .x2

theorem run (o : Oracle) (m : Model) (ord c : Nat) (i : Index) (k : Key) (ent : Entry m ord i)
    (header : KeyRegion m.mem k) (stack : m.reg .x6=wordAddress replyBase) (cursor : m.reg .x7=W c)
    (proof : m.reg .x25=wordAddress base) (room : (c+64)/64<capacity)
    (s : MachineState) (pc : s.pc=addr 143) (fits : Fits s m) :
    ∃ t n, CommitExact.Segment o OpeningStraight.image (steps c i) s t ∧ t.pc=addr 237 ∧
      Fits t n ∧ Result o m n k ord c i := by
  let a := answer o m ord i
  let l := laneOf i
  let v := replyWords (tapeReply o k i) (LeafNonce.firstWord l)
  let w := replyWords (tapeReply o k i) (LeafNonce.nextWord l)
  have limit : c+64<2^64 := by unfold capacity at room;omega
  have firstRoom : c/64<capacity := by omega
  obtain ⟨u,ru,pu,hu⟩ := query_run o m ord i ent s pc fits
  have ready := (setup o m ord i ent).2.1
  obtain ⟨az,as_,ac,af,atree,ap,atag⟩ := kept o m ord i
  obtain ⟨b,m₁,rb,pb,hb,loaded⟩ := OpeningLane.select o a i u pu hu (az.trans ent.zero) (as_.trans stack)
    ready.prod ready.slot
  have r1 (r : Reg) (untouched : r≠.x10 ∧ r≠.x11 ∧ r≠.x12) : m₁.reg r=a.reg r :=
    loaded.frame r untouched.1 untouched.2.1 untouched.2.2
  have low : m₁.reg .x12=v := loaded.low.trans (reply o m ord k i ent header _)
  have m1zero : m₁.reg .x0=0 := (r1 _ (by decide)).trans (az.trans ent.zero)
  have m1cursor : m₁.reg .x7=W c := (r1 _ (by decide)).trans (ac.trans cursor)
  have m1proof : m₁.reg .x25=wordAddress base := (r1 _ (by decide)).trans (ap.trans proof)
  let m₂ := OpeningSaltLow.finish m₁ c
  obtain ⟨p,rp,pp,hp,mem2,r2⟩ := OpeningSaltLow.run o m₁ c firstRoom b pb hb m1zero m1cursor m1proof
  have m2mem : m₂.mem=put a.mem c 64 v := by rw [show m₂.mem=_ from mem2,loaded.memory,low]
  have m2frame (r : Reg) (h : r≠.x10 ∧ r≠.x13 ∧ r≠.x12 ∧ r≠.x14 ∧ r≠.x16 ∧ r≠.x17) : m₂.reg r=m₁.reg r :=
    r2 r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  have m2stack := (m2frame .x6 (by decide)).trans ((r1 _ (by decide)).trans (as_.trans stack))
  have m2idx := (m2frame .x11 (by decide)).trans loaded.offset
  let m₃ := after m₂ (OpeningSaltHigh.loadOps l)
  obtain ⟨q,rq,pq,hq⟩ := OpeningSaltHigh.load_run o m₂ l p pp hp m2stack m2idx
  have m2cursor := (m2frame .x7 (by decide)).trans m1cursor
  have m2proof := (m2frame .x25 (by decide)).trans m1proof
  obtain ⟨value,dest,mem3,r3⟩ := OpeningSaltHigh.loaded m₂ c l limit m2cursor m2proof
  have m3zero := (r3 .x0 (by decide) (by decide) (by decide)).trans ((m2frame _ (by decide)).trans m1zero)
  have m3off : m₃.reg .x10=W ((c+64)%64) := by
    rw [show (c+64)%64=c%64 by omega]
    exact (r3 _ (by decide) (by decide) (by decide)).trans
      (OpeningSaltLow.exit_offset m₁ c (by omega) m1cursor m1proof)
  have small := OpeningSaltLow.room (c+64) room
  let m₄ := OpeningSaltHigh.output m₃ (c+64)
  obtain ⟨endState,last,atEnd,matched⟩ := OpeningSaltHigh.write_run o m₃ (c+64) small q pq hq m3zero m3off dest
  have val : m₃.reg .x12=OpeningSaltHigh.clip w := by
    rw [show m₃.reg .x12=_ from value,m2mem,fits_after_low c room l a.mem v]
    exact congrArg OpeningSaltHigh.clip (reply o m ord k i ent header _)
  have pass (r : Reg) (safe : r≠.x10 ∧ r≠.x11 ∧ r≠.x12 ∧ r≠.x13 ∧ r≠.x14 ∧ r≠.x16 ∧ r≠.x17) :
      m₄.reg r=a.reg r := by
    obtain ⟨x,y,z,v,w,b,e⟩ := safe
    exact (OpeningSaltHigh.frame _ _ _ x v w).trans ((r3 _ y z v).trans
      ((m2frame _ ⟨x,v,z,w,b,e⟩).trans (r1 _ ⟨x,y,z⟩)))
  refine ⟨endState,m₄,CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose ru rb) rp) rq) last,
    atEnd,matched,?_,(pass _ (by decide)).trans ready.index,(pass _ (by decide)).trans (ac.trans cursor),
    (pass _ (by decide)).trans af,(pass _ (by decide)).trans atree,(pass _ (by decide)).trans ap,
    (pass _ (by decide)).trans az,(pass _ (by decide)).trans (stackPointer o m ord i)⟩
  have result := OpeningSaltHigh.memory m₃ (c+64) m3zero m3off
  rw [result,show m₃.mem=_ from mem3,m2mem,val]

end CommitGolfCandidate.Reconstruction.OpeningRecordSalt
