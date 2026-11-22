import CommitGolfCandidate.Layout2WriterTrack
namespace CommitGolfCandidate.Layout2Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

private theorem shr_num (a k : Nat) (fit : a<2^64) : addr a >>> k=addr (a >>> k) := by
  have bound : a >>> k<2^64 := by rw [Nat.shiftRight_eq_div_pow];exact (Nat.div_le_self _ _).trans_lt fit
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,Nat.mod_eq_of_lt bound]

private theorem scale5 (a : Nat) : addr a <<< (5:Nat)=addr (32*a) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow];change addr a * addr 32=_
  rw [←BitVec.ofNat_mul,Nat.mul_comm]
private theorem scale10 (a : Nat) : addr a <<< (10:Nat)=addr (1024*a) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow];change addr a * addr 1024=_
  rw [←BitVec.ofNat_mul,Nat.mul_comm]

private theorem add_addr (a b : Nat) : addr a+addr b=addr (a+b) := (BitVec.ofNat_add ..).symm
private theorem mask3 (a : Nat) (fit : a<2^64) : addr a &&& 3#64=addr (a%4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,show (3#64).toNat=2^2-1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a%4<2^64 by omega)]

private theorem imm8 (i : Nat) (small : i<68) : signExtend12 (BitVec.ofNat 12 (8*i))=addr (8*i) := by
  interval_cases i <;> rfl
private theorem imm32 (i : Nat) (small : i<4) : signExtend12 (BitVec.ofNat 12 (32*i))=addr (32*i) := by
  interval_cases i <;> rfl
private theorem node_bound {pos : Nat} (small : pos<16777216) (l : Nat) : node pos l<2^64 := by
  unfold node;rw [Nat.shiftRight_eq_div_pow];exact (Nat.div_le_self _ _).trans_lt (by omega)

theorem progress {s m p pos B l22 c v} (e : PhaseEntry s p pos B l22 c) (h : Track s m p pos B l22 c v)
    (r : Row) (ok : pre p v r) :
    memoryArgumentsValid m (instruction r)=true ∧ Track s (execInstrBr m (instruction r)) p pos B l22 c (advance v r) := by
  have heap : m.getReg .x9=addr heapBase := (h.fixed _ (by decide)).trans e.heap
  have slots : m.getReg .x18=addr (slotBase+584) := (h.fixed _ (by decide)).trans e.slots
  have leaves : m.getReg .x19=addr 4194304 := (h.fixed _ (by decide)).trans e.leaves
  have dest : m.getReg .x21=addr B := (h.fixed _ (by decide)).trans e.dest
  have posSmall:=e.index
  have room:=e.room.2
  have limit : MEMORY_BYTES<2^64 := by decide
  cases r with
  | residue =>
    have src : m.getReg .x6=addr pos := h.readAs .n ok
    refine ⟨rfl,h.assign .a .residue _ _ ?_⟩
    change m.getReg .x6 &&& signExtend12 3=addr (pos%4)
    rw [src,show signExtend12 3=3#64 from rfl,mask3 _ (by omega)]
  | selector =>
    have src : m.getReg .x10=addr (pos%4) := h.readAs .a ok
    refine ⟨rfl,h.assign .a .selector _ _ ?_⟩
    change m.getReg .x10 <<< (5:Nat)=_
    rw [src];exact scale5 _
  | quartet =>
    have src : m.getReg .x6=addr pos := h.readAs .n ok
    refine ⟨rfl,h.assign .n .quartet _ _ ?_⟩
    change m.getReg .x6 >>> (2:Nat)=addr (pos/4)
    rw [src,shr_num _ _ (by omega),Nat.shiftRight_eq_div_pow]
  | groupDelta =>
    have src : m.getReg .x6=addr (pos/4) := h.readAs .n ok
    refine ⟨rfl,h.assign .ptr .groupDelta _ _ ?_⟩
    change m.getReg .x6 <<< (10:Nat)=_
    rw [src];exact scale10 _
  | groupBase =>
    have src : m.getReg .x7=addr (1024*(pos/4)) := h.readAs .ptr ok
    refine ⟨rfl,h.assign .ptr .grp _ _ ?_⟩
    change m.getReg .x7+m.getReg .x18=addr (group pos)
    rw [src,slots,add_addr,group,Nat.add_comm]
  | mateOffset f =>
    have src : m.getReg .x10=addr (32*(pos%4)) := h.readAs .a ok.1
    refine ⟨rfl,h.assign .aux (.mate f) _ _ ?_⟩
    change m.getReg .x10 ^^^ signExtend12 (BitVec.ofNat 12 (32*f))=addr (mateOffset pos f)
    rw [src,imm32 _ ok.2.2,←BitVec.ofNat_xor];rfl
  | mateBase f =>
    have x : m.getReg .x28=addr (mateOffset pos f) := h.readAs .aux ok.1
    have y : m.getReg .x7=addr (group pos) := h.readAs .ptr ok.2.1
    refine ⟨rfl,h.assign .aux (.base f) _ _ ?_⟩
    change m.getReg .x28+m.getReg .x7=addr (fieldBase l22 pos f)
    rw [x,y,add_addr,fieldBase,if_neg (Nat.ne_of_gt ok.2.2.1),if_pos ok.2.2.2,Nat.add_comm]
  | pointer =>
    have ptr : m.getReg .x7=addr (group pos) := h.readAs .ptr ok
    have a : m.getReg .x7+signExtend12 128=addr (group pos+128) := by rw [ptr];exact add_addr _ _
    refine ⟨?_,h.assign .ptr (.base 4) _ _ ?_⟩
    · change accessValid _ 8=true
      rw [a];apply access8
      · unfold group slotBase;omega
      · unfold group slotBase MEMORY_BYTES;omega
    · change m.getMem (m.getReg .x7+signExtend12 128)=addr (fieldBase l22 pos 4)
      rw [a,h.pointer_word e];rfl
  | root =>
    have n : m.getReg .x6=addr (pos/4) := h.readAs .n ok
    refine ⟨rfl,h.assign .n (.node 0) _ _ ?_⟩
    change m.getReg .x6+m.getReg .x19=addr (node pos 0)
    rw [n,leaves,add_addr];simp [node,Nat.add_comm]
  | ascend l =>
    have n : m.getReg .x6=addr (node pos l) := h.readAs .n ok
    refine ⟨rfl,h.assign .n (.node (l+1)) _ _ ?_⟩
    change m.getReg .x6 >>> (1:Nat)=addr (node pos (l+1))
    rw [n,shr_num _ _ (node_bound posSmall l)]
    exact congrArg addr (Nat.shiftRight_add _ _ _).symm
  | flip l =>
    have n : m.getReg .x6=addr (node pos l) := h.readAs .n ok
    refine ⟨rfl,h.assign .ptr (.flipped l) _ _ ?_⟩
    change m.getReg .x6 ^^^ signExtend12 1=_
    rw [n,show signExtend12 1=addr 1 from rfl,←BitVec.ofNat_xor];rfl
  | scale l =>
    have n : m.getReg .x7=addr (node pos l ^^^ 1) := h.readAs .ptr ok
    refine ⟨rfl,h.assign .ptr (.scaled l) _ _ ?_⟩
    change m.getReg .x7 <<< (5:Nat)=_;rw [n];exact scale5 _
  | sibling l =>
    have n : m.getReg .x7=addr (32*(node pos l ^^^ 1)) := h.readAs .ptr ok.1
    refine ⟨rfl,h.assign .ptr (.base (4+l)) _ _ ?_⟩
    change m.getReg .x9+m.getReg .x7=addr (fieldBase l22 pos (4+l))
    rw [heap,n,add_addr];simp [fieldBase,show ¬4+l<4 by omega, show 4+l≠4 by have:=ok.2;omega,Nat.ne_of_gt ok.2]
  | load d b f j =>
    have src : m.getReg b.reg=addr (fieldBase l22 pos f) := h.readAs b ok.1
    have inside:=ok.2;have wid : width f≤32 := by unfold width;split <;> decide
    have a : m.getReg b.reg+signExtend12 (BitVec.ofNat 12 (8*j))=addr (fieldBase l22 pos f+8*j) := by
      rw [src,imm8 _ (by omega),add_addr]
    have bounds:=field_geometry e f
    refine ⟨?_,h.assign d (.data (start f+8*j)) _ _ ?_⟩
    · change accessValid _ 8=true
      rw [a];apply access8 <;> omega
    · change m.getMem (m.getReg b.reg+signExtend12 (BitVec.ofNat 12 (8*j)))=_
      rw [a];exact h.source_word e _ _ inside
  | store t j =>
    have width : stride p≤536 := by unfold stride;split <;> decide
    change 8*j+8≤stride p at ok
    have a : m.getReg .x21+signExtend12 (BitVec.ofNat 12 (8*j))=addr (B+8*j) := by
      rw [dest,imm8 _ (by omega),add_addr]
    refine ⟨?_,?_⟩
    · change accessValid _ 8=true;rw [a];apply access8 <;> have:=e.aligned <;> omega
    · simp only [instruction,execInstrBr,a]
      exact h.store e j (v.reg t) _ _ (h.reg t) ok
  | shl d t n =>
    refine ⟨rfl,h.assign d (.shl (v.reg t) n) _ _ ?_⟩
    change m.getReg t.reg <<< (BitVec.ofNat 6 n).toNat=_
    rw [h.reg,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n<64 from ok)];rfl
  | shr d t n =>
    refine ⟨rfl,h.assign d (.shr (v.reg t) n) _ _ ?_⟩
    change m.getReg t.reg >>> (BitVec.ofNat 6 n).toNat=_
    rw [h.reg,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n<64 from ok)];rfl
  | bor d x y =>
    refine ⟨rfl,h.assign d (.bor (v.reg x) (v.reg y)) _ _ ?_⟩
    change m.getReg x.reg ||| m.getReg y.reg=_;rw [h.reg,h.reg];rfl

end CommitGolfCandidate.Layout2Writer
