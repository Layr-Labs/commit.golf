import CommitGolfCandidate.S4Inputs
import CommitGolfCandidate.S4CarryState
import CommitGolfCandidate.S4Stores
namespace CommitGolfCandidate.S4.Codec
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open Carry (carrier prev delta group pieces source part)
def original (s : MachineState) (a : Nat) := byte s (proofBase+a)
def Mem (d : Bool) (s t : MachineState) (k c : Nat) := ∀ q,q<2^64 →
  byte t q=if proofBase≤q ∧ q<proofBase+70410 then Carry.state d (original s) k c (q-proofBase) else byte s q

theorem memStart (d : Bool) (s : MachineState) : Mem d s s 0 0 := by
  intro q h;split
  · rename_i yes;rw [Carry.start,original,show proofBase+(q-proofBase)=q by omega]
  · rfl

theorem Mem.still {d : Bool} {s t u : MachineState} {k c : Nat} (old : Mem d s t k c) (mem : u.mem=t.mem) :
    Mem d s u k c := by intro q h;exact (show byte u q=byte t q by simp only [byte,MachineState.getByte,MachineState.getMem,mem]).trans (old q h)

theorem Mem.atByte {d : Bool} {s t : MachineState} {k c : Nat} (m : Mem d s t k c) (a : Nat) (h : a<70410) :
    byte t (proofBase+a)=Carry.state d (original s) k c a := by
  have bound : proofBase=12079599648:=rfl
  rw [m _ (by omega),if_pos (by omega),Nat.add_sub_cancel_left]

theorem Mem.field {d : Bool} {s t u : MachineState} {k c : Nat} (m : Mem d s t k c) (bound : c<1309)
    (effect : Wrote t u (proofBase+carrier c) 1 (fun _=>Carry.fieldValue d (original s) c)) : Mem d s u k (c+1) := by
  intro q b
  rw [effect q b,m q b]
  have loc:=(Carry.location _ bound).2
  by_cases yes : q=proofBase+carrier c
  · subst q
    simp only [if_pos (show proofBase+carrier c≤proofBase+carrier c ∧ proofBase+carrier c<proofBase+carrier c+1 by omega),
      if_pos (show proofBase≤proofBase+carrier c ∧ proofBase+carrier c<proofBase+70410 by omega),
      Nat.add_sub_cancel_left,Carry.writeField d (original s) k c _ bound,ite_true]
  · rw [if_neg (by omega : ¬(proofBase+carrier c≤q ∧ q<proofBase+carrier c+1))]
    split
    · rename_i within;rw [Carry.writeField _ _ _ _ _ bound,if_neg (by omega)]
    · rfl

theorem Mem.doneByte {s t u : MachineState} {k c : Nat} (m : Mem true s t k c) (bound : k<330)
    (effect : Wrote t u (proofBase+70080+k) 1 (fun _=>Carry.restored (original s) k)) : Mem true s u (k+1) c := by
  intro q b;rw [effect q b,m q b]
  by_cases yes : q=proofBase+70080+k
  · subst q
    simp only [if_pos (show proofBase+70080+k≤proofBase+70080+k ∧ proofBase+70080+k<proofBase+70080+k+1 by omega),
      if_pos (show proofBase≤proofBase+70080+k ∧ proofBase+70080+k<proofBase+70410 by omega),
      show proofBase+70080+k-proofBase=70080+k by omega,Carry.completeByte,ite_true,true_and]
  · rw [if_neg (by omega : ¬(proofBase+70080+k≤q ∧ q<proofBase+70080+k+1))]
    split
    · rename_i within;rw [Carry.completeByte,if_neg (by omega : ¬(true=true ∧ q-proofBase=70080+k))]
    · rfl

theorem Mem.encByte {s t : MachineState} {k c : Nat} (m : Mem false s t k c) : Mem false s t (k+1) c := by
  intro q h;simpa only [Carry.completeByte,Bool.false_eq_true,false_and,ite_false] using m q h

theorem packed_agrees (f g : Nat→Byte) (same : ∀ j<70410,f j=g j) (a : Nat) (ha : a<70080) :
    Carry.packedAt f a=Carry.packedAt g a := by
  unfold Carry.packedAt;split
  · rename_i used
    have sc : source (Carry.candidate a)<330:=by have:=used.1;unfold source;omega
    dsimp only;rw [same a (by omega),same _ (by omega)]
  · exact same a (by omega)

theorem decoded_agrees (f g : Nat→Byte) (same : ∀ j<70080,f j=g j) (a : Nat) (ha : a<70410) :
    Carry.wideAt f a=Carry.wideAt g a := by
  unfold Carry.wideAt;split
  · rename_i small;rw [same a small]
  · rename_i large
    let k:=a-70080
    have hk : k<330:=by dsimp only [k];omega
    have eqv (p : Nat) (h : p<pieces k) : f (carrier (group k p))=g (carrier (group k p)):=
      same _ (Carry.location _ (Carry.groupSpec _ _ hk h).1).2
    change Carry.restored f k=Carry.restored g k
    unfold Carry.restored
    dsimp only
    by_cases last : k%30=29
    · simp only [if_pos last,eqv 0 (by simp [pieces,last]),eqv 1 (by simp [pieces,last]),eqv 2 (by simp [pieces,last])]
    · simp only [if_neg last,eqv 0 (by simp [pieces,last]),eqv 1 (by simp [pieces,last]),eqv 2 (by simp [pieces,last]),eqv 3 (by simp [pieces,last])]

end CommitGolfCandidate.S4.Codec
