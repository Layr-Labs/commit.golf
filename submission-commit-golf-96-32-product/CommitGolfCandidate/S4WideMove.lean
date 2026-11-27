import CommitGolfCandidate.S4ByteFrame
import CommitGolfCandidate.TruncHalf

namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem wordNumber {a b : Nat} (ba : a<2^64) (bb : b<2^64) (e : W a=W b) : a=b := by
  have h:=congrArg BitVec.toNat e
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ba,Nat.mod_eq_of_lt bb] using h

def copyHalf (s : MachineState) (src dst : Nat) := s.setHalfword (W dst) (s.getHalfword (W src))
theorem movedHalf (s : MachineState) (src dst : Nat) (bs : src+2≤2^64) (bd : dst+2≤2^64)
    (asrc : src%2=0) (adst : dst%2=0) : Moved s (copyHalf s src dst) src dst 2 := by
  have al (a : Nat) (b : a+2≤2^64) (e : a%2=0) : (W a).toNat%2=0 := by
    simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^64)] using e
  obtain ⟨lo,hi⟩:=Trunc.Wire.copy_bytes s (W src) (W dst) (al _ bs asrc) (al _ bd adst)
  intro q bq;by_cases inside : dst≤q ∧ q<dst+2
  · rw [if_pos inside]
    rcases (show q=dst ∨ q=dst+1 by omega) with a|a
    · subst q;rw [Nat.sub_self,Nat.add_zero];exact lo
    · subst q;rw [Nat.add_sub_cancel_left]
      change (s.setHalfword (W dst) (s.getHalfword (W src))).getByte (W (dst+1))=s.getByte (W (src+1))
      rw [show W (dst+1)=W dst+1 from BitVec.ofNat_add ..,show W (src+1)=W src+1 from BitVec.ofNat_add ..];exact hi
  · rw [if_neg inside]
    apply Trunc.Wire.store_outside _ _ _ _ (al _ bd adst)
    constructor
    · intro e;have:=wordNumber bq (by omega) e;omega
    · intro e;have h : W q=W (dst+1):=e.trans (BitVec.ofNat_add ..).symm
      have:=wordNumber bq (by omega) h;omega

theorem byteWord (s : MachineState) (a : Nat) :
    byte s a=extractByte (s.getMem (W (8*(a/8)))) (a%8) := by
  simpa only [Nat.div_add_mod a 8,Nat.div_eq_of_lt (Nat.mod_lt a (by decide : 0<8)),Nat.mul_zero,Nat.add_zero,
    Nat.mod_eq_of_lt (Nat.mod_lt a (by decide : 0<8)),byte,W] using aligned_byte s (a/8) (a%8) (by omega)

def copyDword (s : MachineState) (src dst : Nat) := s.setMem (W dst) (s.getMem (W src))
theorem movedDword (s : MachineState) (src dst : Nat) (bd : dst+8≤2^64)
    (asrc : src%8=0) (adst : dst%8=0) : Moved s (copyDword s src dst) src dst 8 := by
  intro q bq
  by_cases inside : dst≤q ∧ q<dst+8
  · rw [if_pos inside,byteWord,byteWord s,show 8*(q/8)=dst by omega,
      show 8*((src+(q-dst))/8)=src by omega,show (src+(q-dst))%8=q%8 by omega]
    unfold copyDword;rw [MachineState.getMem_setMem_eq]
  · have distinct : W (8*(q/8))≠W dst:=by intro e;have h:=wordNumber (by omega) (by omega) e;omega
    rw [if_neg inside,byteWord,byteWord s];unfold copyDword
    rw [MachineState.getMem_setMem_ne distinct]

private theorem parts (a : Nat) : alignToDword (W a)=W (8*(a/8)) ∧ byteOffset (W a)=a%8 := by
  have off : byteOffset (W a)=a%8 := by
    unfold byteOffset W;rw [BitVec.toNat_and,BitVec.toNat_ofNat]
    change a%2^64 &&& (2^3-1)=a%8
    rw [Nat.and_two_pow_sub_one_eq_mod];omega
  have top : alignToDword (W a)=W (a-a%8) := by
    change (W a &&& ~~~(7 : Word))=_
    have e : W a &&& (7 : Word)=W (a%8) := by
      apply BitVec.eq_of_toNat_eq
      change byteOffset (W a)=(a%8)%2^64;rw [off];omega
    have mask : (W a &&& ~~~(7 : Word))+(W a &&& (7 : Word))=W a := by
      rw [BitVec.add_eq_or_of_and_eq_zero]
      · ext i;simp only [BitVec.getElem_or,BitVec.getElem_and,BitVec.getElem_not];cases k : (7#64)[i] <;> simp
      · ext i;simp only [BitVec.getElem_and,BitVec.getElem_not];cases k : (7#64)[i] <;> simp
    rw [e] at mask
    have eqv : W (a-a%8)+W (a%8)=W a:=by rw [←BitVec.ofNat_add];exact congrArg W (by omega)
    have h:=congrArg (fun t : Word=>t-W (a%8)) (mask.trans eqv.symm)
    simpa only [BitVec.add_sub_cancel] using h
  exact ⟨top.trans (congrArg W (by omega)),off⟩

private theorem part32 (old src : Word) (u v i : Nat) (bu : u<2) (bv : v<2) (bi : i<8) :
    extractByte (replaceWord32 old u (extractWord32 src v)) i =
      if i/4=u then extractByte src (4*v+i%4) else extractByte old i := by
  interval_cases u <;> interval_cases v <;> interval_cases i <;>
    simp (config:={decide:=true}) [extractByte,replaceWord32,extractWord32] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro bit bounded <;> interval_cases bit <;> simp

def copyWord (s : MachineState) (src dst : Nat) := s.setWord32 (W dst) (s.getWord32 (W src))
theorem movedWord (s : MachineState) (src dst : Nat) (bd : dst+4≤2^64)
    (asrc : src%4=0) (adst : dst%4=0) : Moved s (copyWord s src dst) src dst 4 := by
  intro q bq;rw [byteWord];unfold copyWord MachineState.setWord32 MachineState.getWord32
  simp only [(parts dst).1,(parts dst).2,(parts src).1,(parts src).2]
  by_cases same : 8*(q/8)=8*(dst/8)
  · rw [same,MachineState.getMem_setMem_eq,part32 _ _ _ _ _ (by omega) (by omega) (by omega)]
    by_cases inside : dst≤q ∧ q<dst+4
    · rw [if_pos inside,if_pos (by omega),byteWord]
      rw [show 8*((src+(q-dst))/8)=8*(src/8) by omega,show (src+(q-dst))%8=4*(src%8/4)+q%8%4 by omega]
    · rw [if_neg inside,if_neg (by omega),byteWord,same]
  · have distinct : W (8*(q/8))≠W (8*(dst/8)):=fun e=>same (wordNumber (by omega) (by omega) e)
    rw [MachineState.getMem_setMem_ne distinct,if_neg (by omega),byteWord]
end CommitGolfCandidate.S4.Machine
