import CommitGolfCandidate.Layout2Phase
import CommitGolfCandidate.Memory

namespace CommitGolfCandidate.Layout2Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase
set_option maxHeartbeats 1400000
abbrev addr := BitVec.ofNat 64
def start (f : Nat) := if f=0 then 0 else 16+32*(f-1)
def width (f : Nat) := if f=0 then 16 else 32
def node (pos l : Nat) := (4194304+pos/4) >>> l
def group (pos : Nat) := slotBase+584+1024*(pos/4)
def mateOffset (pos f : Nat) := (32*(pos%4)) ^^^ (32*f)
def fieldBase (l22 pos f : Nat) :=
  if f=0 then saltBase+16*pos else if f<4 then group pos+mateOffset pos f
  else if f=4 then l22 else heapBase+32*(node pos (f-4) ^^^ 1)

theorem source_offset (l22 pos f j : Nat) (inside : j<width f) :
    sourceAddress l22 pos (start f+j)=fieldBase l22 pos f+j := by
  by_cases zero : f=0
  · subst f
    change j<16 at inside
    simp [start,fieldBase,sourceAddress,inside]
  · have size : j<32 := by simpa [width,zero] using inside
    have begin : start f=16+32*(f-1) := by simp [start,zero]
    have l16 : ¬start f+j<16 := by omega
    by_cases mate : f<4
    · have l112 : start f+j<112 := by omega
      simp only [sourceAddress,if_neg l16,if_pos l112,fieldBase,if_neg zero,if_pos mate,
        show (start f+j-16)/32+1=f by omega,show (start f+j-16)%32=j by omega,group,mateOffset]
    · have l112 : ¬start f+j<112 := by omega
      by_cases quad : f=4
      · subst f
        have l144 : start 4+j<144 := by omega
        simp only [sourceAddress,if_neg l16,if_neg l112,if_pos l144,fieldBase,if_neg zero,if_neg mate,
          ite_true,show start 4+j-112=j by omega]
      · have l144 : ¬start f+j<144 := by omega
        simp only [sourceAddress,if_neg l16,if_neg l112,if_neg l144,fieldBase,if_neg zero,if_neg mate,if_neg quad,
          show (start f+j-112)/32=f-4 by omega,show (start f+j-112)%32=j by omega,node]

private theorem mate_numeric (i f : Nat) (hi : i<4) (hf : f<4) :
    ((32*i) ^^^ (32*f))%8=0 ∧ ((32*i) ^^^ (32*f))<128 := by
  interval_cases i <;> interval_cases f <;> decide

theorem field_geometry {s p pos B l22 c} (e : PhaseEntry s p pos B l22 c) (f : Nat) :
    fieldBase l22 pos f%8=0 ∧ fieldBase l22 pos f+width f≤B := by
  have bound:=e.index;have lo:=e.room.1;unfold recordBase0 at lo
  by_cases zero : f=0
  · subst f;simp only [fieldBase,width,ite_true,saltBase];omega
  · by_cases mate : f<4
    · have facts:=mate_numeric (pos%4) f (by omega) mate
      simp only [fieldBase,if_neg zero,if_pos mate,width,group,slotBase,mateOffset]
      omega
    · by_cases quad : f=4
      · have a:=e.quad;unfold saltBase at a
        simp only [fieldBase,width,if_neg zero,if_neg mate,if_pos quad]
        omega
      · have h : node pos (f-4)<2^23 := by
          unfold node;rw [Nat.shiftRight_eq_div_pow];apply lt_of_le_of_lt (Nat.div_le_self _ _);omega
        have x:=Nat.xor_lt_two_pow h (by decide : 1<2^23)
        simp only [fieldBase,width,if_neg zero,if_neg mate,if_neg quad,heapBase];omega

theorem aligned_byte' (s : MachineState) (S j : Nat) (alg : S%8=0) (small : j<8) :
    s.getByte (addr (S+j))=extractByte (s.getMem (addr S)) j := by
  have h:=aligned_byte s (S/8) j (by omega)
  simpa only [show 8*(S/8)=S by omega, Nat.div_eq_of_lt small, Nat.mul_zero,Nat.add_zero,
    Nat.mod_eq_of_lt small] using h

private theorem concatenate (x : Word) :
    extractByte x 7 ++ extractByte x 6 ++ extractByte x 5 ++ extractByte x 4 ++
    extractByte x 3 ++ extractByte x 2 ++ extractByte x 1 ++ extractByte x 0=x := by
  apply BitVec.eq_of_getLsbD_eq;intro b hb
  simp only [BitVec.getLsbD_append,extractByte,BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight]
  interval_cases b <;> simp

theorem input_word {s p pos B l22 c} (e : PhaseEntry s p pos B l22 c) (f j : Nat)
    (inside : 8*j+8≤width f) :
    dwordOf (recordSource s l22 pos) (start f+8*j)=s.getMem (addr (fieldBase l22 pos f+8*j)) := by
  have facts:=field_geometry e f
  have byte (b : Nat) (hb : b<8) : recordSource s l22 pos (start f+8*j+b)=
      extractByte (s.getMem (addr (fieldBase l22 pos f+8*j))) b := by
    unfold recordSource
    rw [Nat.add_assoc,source_offset l22 pos f (8*j+b) (by omega),←Nat.add_assoc]
    exact aligned_byte' _ _ _ (by omega) hb
  have b0 : recordSource s l22 pos (start f+8*j) = extractByte (s.getMem (addr (fieldBase l22 pos f+8*j))) 0 := by simpa only [Nat.add_zero] using byte 0 (by decide)
  simp only [dwordOf,byte _ (by decide : 7<8),byte _ (by decide : 6<8),byte _ (by decide : 5<8),
    byte _ (by decide : 4<8),byte _ (by decide : 3<8),byte _ (by decide : 2<8),byte _ (by decide : 1<8),b0,concatenate]

theorem extract_eq (x : Word) (j : Nat) : extractByte x j=x.extractLsb' (8*j) 8 := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  simp [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', Nat.mul_comm]

theorem access8 (a : Nat) (alg : a%8=0) (room : a+8≤MEMORY_BYTES) : accessValid (addr a) 8=true := by
  have small : a<2^64 := by unfold MEMORY_BYTES at room;omega
  unfold accessValid rangeValid
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small];simp [alg,room]

end CommitGolfCandidate.Layout2Writer
