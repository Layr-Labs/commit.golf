import CommitGolfCandidate.ReconstructedCheckEntry
import CommitGolfCandidate.ReconstructedCheckLeafPhysical

namespace CommitGolfCandidate.Reconstruction.CheckRecordStart
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded LeafModel CheckEntry
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxHeartbeats 1300000
set_option maxRecDepth 18000

def geometry (fp i : Nat) : CheckLeafGeometry.Geometry :=
  ⟨8*(fp-300),8*(valuesBase+32*i)⟩

def nonce (m : Model) : Words 2 := ![m.reg .x14,(m.reg .x10 <<< (8 : Nat)) >>> (8 : Nat)]

structure Contents (m : Model) (fp i : Nat) (idx : Index) (msg : Words 32) : Prop where
  entry : CheckEntry.Entry m fp i
  index : m.mem (indexBase+i)=W idx.val
  marker : m.mem (fp-298)=3633
  message : ∀ j : Fin 32,m.mem (valuesBase+32*i+j.val)=msg j
  beginCopy : m.reg .x6=wordAddress (fp-291)
  endCopy : m.reg .x7=wordAddress (fp-259)
  apart : fp≤valuesBase+32*i ∨ valuesBase+32*i+32≤fp-300

theorem placed (m : Model) (fp i : Nat) (idx : Index) (msg : Words 32) (h : Contents m fp i idx msg) :
    CheckLeafGeometry.Placed (geometry fp i) := by
  have room:=h.entry.fpRoom;have j:=h.entry.slot;have a:=h.apart
  unfold valuesBase at a
  constructor <;> change _ <;> simp only [geometry,valuesBase,MEMORY_BYTES] <;> omega

theorem positive (o : Oracle) (m : Model) (fp i : Nat) (idx : Index) (msg : Words 32) (h : Contents m fp i idx msg)
    (s : MachineState) (pc : s.pc=CommitBlocks.addr 175) (fits : Fits s m) :
    let v:=OpeningQuery.after m (ops fp i)
    ∃ u t, Segment o 218 s t (CheckLeaf.rows o idx (nonce m) msg) ∧ Fits u v ∧
      CheckLeafPhysical.Post u t (geometry fp i) (leafDigestW 240 (o.permutation (CheckLeafCall.request o idx (nonce m) msg 1))) ∧
      t.getReg .x23=W idx.val+16777216#64 ∧ t.getReg .x24=m.reg .x24+222 ∧
      t.getReg .x20=m.reg .x11 >>> (32 : Nat) ∧
      t.getReg .x25=(m.reg .x11 <<< (32 : Nat)) >>> (32 : Nat) ∧
      t.getReg .x18=(m.reg .x12 <<< (32 : Nat)) >>> (32 : Nat) ∧
      t.getReg .x27=(m.reg .x12 >>> (32 : Nat)) &&& 63#64 := by
  let v:=OpeningQuery.after m (ops fp i)
  obtain ⟨u,begin,atLeaf,uf,vals,index,heap,hi,cursor,copy,head1,head3,writes⟩:=CheckEntry.positive o m fp i h.entry s pc fits
  have room:=h.entry.fpRoom;have ord:=h.entry.slot
  have word (j : Nat) (inside : j<2^33) (other : j≠fp-297) : u.getMem (wordAddress j)=m.mem j := by
    have read:=uf.memory j inside
    change u.getMem (wordAddress j)=_ at read
    rw [read,writes,writeWord,ite_eq_right other]
  have origin (k n : Nat) (equal : 8*(fp-300)+n=8*k) : BitVec.ofNat 64 ((geometry fp i).frame+n)=wordAddress k :=
    congrArg W equal
  have args : CheckLeafPhysical.Called u (geometry fp i) idx (nonce m) msg := by
    constructor
    · exact atLeaf
    · rw [uf.registers];change m.reg .x8=_
      rw [h.entry.frame,origin fp 2400 (by omega)]
    · exact (uf.registers _).trans vals
    · rw [uf.registers];change m.reg .x6=_
      rw [h.beginCopy,origin (fp-291) 72 (by omega)]
    · rw [uf.registers];change m.reg .x7=_
      rw [h.endCopy,origin (fp-259) 328 (by omega)]
    · rw [uf.registers,copy,h.beginCopy,origin (fp-291) 72 (by omega)]
    · rw [uf.registers,index,h.index]
    · rw [uf.registers];rfl
    · rw [uf.registers,hi];rfl
    · intro j
      have actual : BitVec.ofNat 64 ((geometry fp i).message+8*j.val)=wordAddress (valuesBase+32*i+j.val) :=
        congrArg W (by change 8*(valuesBase+32*i)+8*j.val=8*(valuesBase+32*i+j.val);omega)
      rw [actual,word _ (by unfold valuesBase;have:=j.isLt;omega) (by have:=j.isLt;have:=h.apart;omega)]
      exact h.message j
    · rw [origin (fp-298) 16 (by omega),word _ (by omega) (by omega)];exact h.marker
  obtain ⟨t,leaf,post⟩:=CheckLeafPhysical.positive o u (geometry fp i) (placed m fp i idx msg h) idx (nonce m) msg args
  refine ⟨u,t,by simpa only [List.nil_append] using compose begin leaf,uf,post,?_,?_,?_,?_,?_,?_⟩
  · rw [post.saved .x23 (by decide),uf.registers,heap,h.index]
  · rw [post.saved .x24 (by decide),uf.registers,cursor]
  · rw [post.saved .x20 (by decide),uf.registers,head1]
  · rw [post.headLow,uf.registers];rfl
  · rw [post.headThird,uf.registers];rfl
  · rw [post.headHigh,uf.registers,head3]

end CommitGolfCandidate.Reconstruction.CheckRecordStart
