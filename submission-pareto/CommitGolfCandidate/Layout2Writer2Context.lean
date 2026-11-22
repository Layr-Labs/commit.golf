import CommitGolfCandidate.Layout2Writer2Program
import CommitGolfCandidate.Layout2WriterTrack
namespace CommitGolfCandidate.Layout2Writer2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase Layout2Writer
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

structure Core (a : MachineState) (p pos B l22 : Nat) (c : Word) : Prop where
  index : pos<16777216
  aligned : B%8=0
  room : recordBase0 ≤ B ∧ B+stride p≤MEMORY_BYTES
  quad : l22%8=0 ∧ heapBase≤l22 ∧ l22+32≤saltBase
  posReg : a.getReg .x6=addr pos
  ptr : a.getReg .x7=addr l22
  slot : a.getReg .x28=addr (B+32*(pos%4))
  dest : a.getReg .x21=addr B
  carry : a.getReg .x11=c
  heap : a.getReg .x9=addr heapBase
  leaves : a.getReg .x19=addr 4194304

theorem begin_track {a p pos B l22 c} (e : Core a p pos B l22 c) : Track a a p pos B l22 c start2 := by
  refine ⟨?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
  intro t
  cases t with
  | n => exact e.posReg
  | ptr => exact e.ptr
  | c => exact e.carry
  | _ => rfl

theorem geometry {s p pos B l22 c} (e : Core s p pos B l22 c) (f : Nat) (large : 4≤f) :
    fieldBase l22 pos f%8=0 ∧ fieldBase l22 pos f+width f≤B := by
  have index:=e.index;have lo:=e.room.1;unfold recordBase0 at lo
  by_cases quad : f=4
  · have a:=e.quad;unfold saltBase at a
    simp only [fieldBase,width,if_neg (by omega : f≠0),if_neg (by omega : ¬f<4),if_pos quad];omega
  · have h : node pos (f-4)<2^23 := by
      unfold node;rw [Nat.shiftRight_eq_div_pow];apply lt_of_le_of_lt (Nat.div_le_self _ _);omega
    have x:=Nat.xor_lt_two_pow h (by decide : 1<2^23)
    simp only [fieldBase,width,if_neg (by omega : f≠0),if_neg (by omega : ¬f<4),if_neg quad,heapBase];omega

private theorem concatenate (x : Word) :
    extractByte x 7 ++ extractByte x 6 ++ extractByte x 5 ++ extractByte x 4 ++
    extractByte x 3 ++ extractByte x 2 ++ extractByte x 1 ++ extractByte x 0=x := by
  apply BitVec.eq_of_getLsbD_eq;intro b hb
  simp only [BitVec.getLsbD_append,extractByte,BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight]
  interval_cases b <;> simp

private theorem input_dword {s p pos B l22 c} (e : Core s p pos B l22 c) (f j : Nat)
    (large : 4≤f) (inside : 8*j+8≤width f) :
    dwordOf (recordSource s l22 pos) (start f+8*j)=s.getMem (addr (fieldBase l22 pos f+8*j)) := by
  have facts:=geometry e f large
  have byte (b : Nat) (hb : b<8) : recordSource s l22 pos (start f+8*j+b)=
      extractByte (s.getMem (addr (fieldBase l22 pos f+8*j))) b := by
    unfold recordSource
    rw [Nat.add_assoc,source_offset l22 pos f (8*j+b) (by omega),←Nat.add_assoc]
    exact aligned_byte' _ _ _ (by omega) hb
  have b0 : recordSource s l22 pos (start f+8*j) = extractByte (s.getMem (addr (fieldBase l22 pos f+8*j))) 0 := by simpa only [Nat.add_zero] using byte 0 (by decide)
  simp only [dwordOf,byte _ (by decide : 7<8),byte _ (by decide : 6<8),byte _ (by decide : 5<8),
    byte _ (by decide : 4<8),byte _ (by decide : 3<8),byte _ (by decide : 2<8),byte _ (by decide : 1<8),b0,concatenate]

theorem store_dword {s m p pos B l22 c v} (e : Core s p pos B l22 c) (h : Track s m p pos B l22 c v)
    (j : Nat) (x : V) (physical newPC : Word) (same : physical=denote s pos l22 c x) (inside : 8*j+8≤stride p) :
    Track s ((m.setMem (addr (B+8*j)) physical).setPC newPC) p pos B l22 c (changeMem v j x) := by
  have room:=e.room.2;have ram : MEMORY_BYTES<2^64 := by decide
  have fit : B+8*j<2^64 := by omega
  refine ⟨h.reg,h.fixed,?_,?_⟩
  · intro i ib
    change (m.setMem _ physical).getMem (addr (B+8*i))=wordAt _ _ _ _ _ i (if i=j then some x else v.out i)
    by_cases eq : i=j
    · subst i;simpa only [MachineState.getMem_setMem_eq,if_pos rfl,ite_true,wordAt] using same
    · have neq : addr (B+8*i)≠addr (B+8*j) := by
        intro g
        have r:=congrArg BitVec.toNat g
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,Nat.mod_eq_of_lt (show B+8*i<2^64 by omega)] at r
        omega
      rw [MachineState.getMem_setMem_ne neq,if_neg eq];exact h.block i ib
  · intro q away
    change (m.setMem _ physical).getMem q=_
    rw [MachineState.getMem_setMem_ne]
    · exact h.frame q away
    · intro eq;rw [eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] at away;omega

theorem read_dword {s m p pos B l22 c v} (e : Core s p pos B l22 c) (h : Track s m p pos B l22 c v)
    (f j : Nat) (large : 4≤f) (inside : 8*j+8≤width f) :
    m.getMem (addr (fieldBase l22 pos f+8*j))=denote s pos l22 c (.data (start f+8*j)) := by
  have room:=e.room.2;have geo:=geometry e f large;have ram : MEMORY_BYTES<2^64:=by decide
  exact (h.frame _ (Or.inl (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show fieldBase l22 pos f+8*j<2^64 by omega)];omega))).trans
    (input_dword e f j large inside).symm

end CommitGolfCandidate.Layout2Writer2
