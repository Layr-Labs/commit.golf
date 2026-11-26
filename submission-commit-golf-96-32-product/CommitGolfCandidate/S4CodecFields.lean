import CommitGolfCandidate.S4CodecBits
import CommitGolfCandidate.S4CodecPiece
import CommitGolfCandidate.S4CodecMemory
namespace CommitGolfCandidate.S4.Codec
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open Carry (group pieces carrier prev prefixValue)
open Late (pcAt)

def lanePC (d : Bool) (k p : Nat) :=
  if p<pieces k then piecePC d k p else bytePC d (k+1)-(if d then 1 else 0)
instance (r : Reg) : Decidable (controlReg r) := inferInstanceAs (Decidable (r∉[Reg.x21,.x6,.x7,.x8]))
def stable (r : Reg) := controlReg r ∧ r≠.x22
instance (r : Reg) : Decidable (stable r) := inferInstanceAs (Decidable (_ ∧ _))
structure Common (d : Bool) (s t : MachineState) (k c : Nat) : Prop where
  memory : Mem d s t k c
  ptr : t.getReg .x21=W (proofBase+Carry.prev c)
  tail : t.getReg .x22=W (proofBase+70080)
  keep : ∀ r,stable r → t.getReg r=s.getReg r
structure Fields (d : Bool) (s t : MachineState) (k p : Nat) extends Common d s t k (group k p) : Prop where
  pc : t.pc=pcAt (lanePC d k p)
  enc : d=false → p<pieces k → t.getReg .x7=shifted (original s (70080+k)) p
  dec : d=true → t.getReg .x8=(prefixValue (original s) k p).zeroExtend 64

theorem fieldStep (law : CodeLaw) (d : Bool) (s t : MachineState) (k p : Nat) (hk : k<330) (hp : p<pieces k) (st : Fields d s t k p) :
    ∃ u,Fields d s u k (p+1) ∧ Runs (program d) t u ((sequence d k p).length) ((sequence d k p).length) := by
  let c:=group k p
  let f:=original s
  let a:=carrier c
  obtain ⟨hc,src,part⟩:=Carry.groupSpec k p hk hp
  change Carry.source c=k at src
  change Carry.part c=p at part
  have bounds:=Carry.location c hc
  have p4 : p<4:=by unfold pieces at hp;split at hp <;> omega
  have old : byte t (proofBase+a)=f a:=(st.memory.atByte a (by omega)).trans (Carry.untouched d f k c hc)
  have ip:=st.pc;rw [lanePC,if_pos hp] at ip
  obtain ⟨u,run⟩:=runPiece law d t proofBase k p hk hp ip st.ptr (by decide)
  have value : (loadedField d (byte t (proofBase+a)) (t.getReg .x7)).truncate 8=Carry.fieldValue d f c := by
    rw [old];cases d with
    | false=>rw [st.enc rfl hp,storeBits _ _ _ p4];simp only [Carry.fieldValue,Bool.false_eq_true,ite_false,src,part];rfl
    | true=>exact storeLow _ _
  have wr : Wrote t u (proofBase+a) 1 (fun _=>Carry.fieldValue d f c) := by
    have e : Wrote t u (proofBase+a) 1 (fun _=>(loadedField d (byte t (proofBase+a)) (t.getReg .x7)).truncate 8):=run.write
    rw [value] at e;exact e
  refine ⟨u,⟨⟨st.memory.field hc wr,?_,(run.keep .x22 (by decide)).trans st.tail,
    fun r h=>(run.keep r h.1).trans (st.keep r h)⟩,run.pc,?_,?_⟩,run.run⟩
  · have next : group k (p+1)=c+1:=rfl
    have prevEq : Carry.prev (group k (p+1))=carrier c:=by
      rw [next,Carry.prev,if_neg (Nat.succ_ne_zero c),Nat.add_sub_cancel]
    rw [prevEq];exact run.ptr
  · intro yes more
    rw [run.shifted yes,if_pos more,st.enc yes hp,shiftMore _ _ p4]
  · intro yes
    rw [run.combined yes,st.dec yes,old,join _ _ _ p4];rfl

theorem fieldLine (law : CodeLaw) (d : Bool) (s t : MachineState) (k p : Nat) (hk : k<330) (hp : p≤pieces k)
    (start : Fields d s t k 0) :
    ∃ u,Fields d s u k p ∧ Runs (program d) t u (lanePC d k p-lanePC d k 0) (lanePC d k p-lanePC d k 0) := by
  induction p with
  | zero=>exact ⟨t,start,by rw [Nat.sub_self];exact Runs.refl _ _⟩
  | succ p ih=>
    obtain ⟨v,mid,path⟩:=ih (by omega)
    obtain ⟨u,last,one⟩:=fieldStep law d s v k p hk (by omega) mid
    have atEnd:=(price d k p hk (by omega)).1
    have hp' : p<pieces k:=by omega
    have pos : 0<pieces k:=by unfold pieces;split <;> decide
    have monotone : lanePC d k 0≤piecePC d k p:=by
      rw [lanePC,if_pos pos];unfold piecePC;split <;> omega
    change piecePC d k p+(sequence d k p).length=lanePC d k (p+1) at atEnd
    have cost : lanePC d k p-lanePC d k 0+(sequence d k p).length=lanePC d k (p+1)-lanePC d k 0:=by
      rw [lanePC,if_pos hp'];omega
    exact ⟨u,last,by simpa only [cost] using path.trans one⟩
end CommitGolfCandidate.S4.Codec
