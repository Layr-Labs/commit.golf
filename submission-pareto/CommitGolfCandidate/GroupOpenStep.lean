import CommitGolfCandidate.K3OpenCopy
import CommitGolfCandidate.K3OpenCall
import CommitGolfCandidate.K1OpenSalt
import CommitGolfCandidate.GroupOpenMemory
import CommitGolfCandidate.GroupOpenTable

/-! First pass, one position: addresses, entry registers and the head paths (rows 3077..3096). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000

def indexAt (j : Nat) := BitVec.ofNat 64 (9395245088+8*j)
def destAt (i : Index) := BitVec.ofNat 64 (9126809632+16*i.val)
def countWord (n : Nat) := BitVec.ofNat 64 n
/-- K1 reply offset of the salt of leaf `i` (`CounterSalt.bitOffset / 8`). -/
def offAt (i : Index) := if rank i.val=0 then 0 else if rank i.val=1 then 184 else 16*(rank i.val-1)
def readAt (i : Index) := BitVec.ofNat 64 (1536+offAt i)
/-- K1 generator counter: the base address of the group's C leaf (`CounterSalt.ctr`). -/
def ctrAt (i : Index) := wordAddress (msgWord (i.val-rank i.val+1))

/-- First word of quartet block `q` (`B_q = trapdoor + 32 L + 1024 q`). -/
def blockWord (q : Nat) := 603980292+128*q
/-- The reply of group `g`: reply_E at `B_g+168` (even `g`), reply_O at `B_{g-1}-32` (odd `g`, the odd block
sits 200 bytes below the even one). -/
def replyWord (g : Nat) := blockWord (2*(g/2))+21-25*(g%2)
/-- Level-22 node of group `h`: reply_E bytes 0..32 at `B_e+168` (even `h`), reply_O bytes 168..200 at `B_e+136`
(odd `h`), `e = 2 (h/2)`. -/
def nodeWordOf (h : Nat) := blockWord (2*(h/2))+21-4*(h%2)
/-- The block the prefix rebuilds from the inverse of group `g`'s reply: `Q + 512 + 1024 g` (both parities). -/
def rebuiltWord (g : Nat) := blockWord g+64
/-- Heap slot of node `n` (trapdoor offset `32 n`). -/
def heapWord (n : Nat) := 536871428+4*n

theorem xor_one (g : Nat) : (g^^^1)/2=g/2 ∧ (g^^^1)%2=1-g%2 := by
  constructor
  · change (g^^^1)/2^1=g/2^1
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib]
    have zero : (1:Nat) >>> 1 = 0 := by decide
    simp [zero]
  · change (g^^^1)%2^1=1-g%2
    rw [Nat.xor_mod_two_pow, Nat.mod_eq_of_lt (by decide : (1:Nat)<2^1)]
    have small : ∀ b<2, b^^^1=1-b := by decide
    exact small (g%2^1) (by omega)

theorem xor_one_lt (g n : Nat) (h : g<2^n) (pos : 0<n) : g^^^1<2^n :=
  Nat.xor_lt_two_pow h (by have : 2^1≤2^n := Nat.pow_le_pow_right (by decide) pos; omega)

theorem shift_right_nat (n k : Nat) (h : n<2^64) : (BitVec.ofNat 64 n >>> k)=BitVec.ofNat 64 (n/2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem shift_left_nat (n k : Nat) : (BitVec.ofNat 64 n <<< k)=BitVec.ofNat 64 (n*2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem nat_and_four (i : Nat) : i &&& 4=4*(i/4%2) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  rcases Nat.mod_two_eq_zero_or_one (i/4) with h|h
  · rw [h, Nat.mul_zero, Nat.zero_testBit]
    by_cases hj : j=2
    · subst hj
      have t : i.testBit 2=false := by rw [Nat.testBit_eq_decide_div_mod_eq]; simp [h]
      rw [t, Bool.false_and]
    · have t : (4:Nat).testBit j=false := by
        rw [show (4:Nat)=2^2 by rfl, Nat.testBit_two_pow]; simp; omega
      rw [t, Bool.and_false]
  · rw [h, Nat.mul_one]
    by_cases hj : j=2
    · subst hj
      have t : i.testBit 2=true := by rw [Nat.testBit_eq_decide_div_mod_eq]; simp [h]
      rw [t, Bool.true_and]
    · have t : (4:Nat).testBit j=false := by
        rw [show (4:Nat)=2^2 by rfl, Nat.testBit_two_pow]; simp; omega
      rw [t, Bool.and_false]

theorem and_four (i : Nat) :
    (BitVec.ofNat 64 i &&& signExtend12 4#12)=BitVec.ofNat 64 (4*(i/4%2)) := by
  rw [show signExtend12 4#12=BitVec.ofNat 64 4 by decide, ← BitVec.ofNat_and, nat_and_four]

theorem xor_low (n : Nat) :
    (BitVec.ofNat 64 n ^^^ signExtend12 1#12)=BitVec.ofNat 64 (n^^^1) := by
  rw [show signExtend12 1#12=BitVec.ofNat 64 1 by decide, ← BitVec.ofNat_xor]

private theorem masked (i : Index) : rv64_remu (BitVec.ofNat 64 i.val) 4096#64=BitVec.ofNat 64 (i.val%4096) := by
  unfold rv64_remu
  apply BitVec.eq_of_toNat_eq
  have h : i.val<16777216:=i.isLt
  simp [BitVec.toNat_umod,BitVec.toNat_ofNat] <;> omega

theorem decoded_rank (i : Index) : rv64_remu (BitVec.ofNat 64 (i.val%4096)) 11=BitVec.ofNat 64 (rank i.val) := by
  unfold rv64_remu rank
  change BitVec.ofNat 64 _ % 11#64=_
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show i.val%4096<2^64 by omega),
    Nat.mod_eq_of_lt (show i.val%4096%11<2^64 by omega)] <;> omega

/-- The counter rows (`sub; addi 1; slli 8; add x26`) in the shape `simp` leaves them. -/
theorem counter_address (i : Index) :
    (BitVec.ofNat 64 i.val - BitVec.ofNat 64 (rank i.val)) <<< (8 : Nat) + 1#64 <<< (8 : Nat) + 4096 = ctrAt i := by
  have sub : rank i.val ≤ i.val := by unfold rank;omega
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by unfold rank;omega) sub,BitVec.shiftLeft_eq_mul_twoPow,
    BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 _*BitVec.ofNat 64 256+BitVec.ofNat 64 1*BitVec.ofNat 64 256+BitVec.ofNat 64 4096=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_mul,←BitVec.ofNat_add,←BitVec.ofNat_add]
  unfold ctrAt wordAddress msgWord;congr 1;omega

theorem salt_address (i : Index) : ((BitVec.ofNat 64 i.val) <<< (4 : Nat))+9126809632=destAt i := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 i.val*BitVec.ofNat 64 16+BitVec.ofNat 64 9126809632=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add];unfold destAt;congr 1 <;> omega

theorem output_address (i : Index) (two : 2≤rank i.val) :
    (((BitVec.ofNat 64 (rank i.val))+signExtend12 (-1)) <<< (4 : Nat))+1536=readAt i := by
  have one : 1≤rank i.val := by omega
  rw [show signExtend12 (-1) = -(BitVec.ofNat 64 1) by decide]
  rw [←BitVec.sub_eq_add_neg]
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) one,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 _*BitVec.ofNat 64 16+BitVec.ofNat 64 1536=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add];unfold readAt offAt
  rw [if_neg (show rank i.val≠0 by omega),if_neg (show rank i.val≠1 by omega)];congr 1 <;> omega

structure Registers (s : MachineState) (ord left : Nat) : Prop where
  output : s.getReg .x12=1536
  selector : s.getReg .x5=0
  width : s.getReg .x11=200
  primitive : s.getReg .x13=1
  index : s.getReg .x14=indexAt ord
  endReg : s.getReg .x17=indexAt (ord+left)
  shift : s.getReg .x25=if left=0 then s.getReg .x9 else BitVec.ofNat 64 (8*(ord+left))
  salt : s.getReg .x22=9126809632
  base : s.getReg .x26=4096

/-- Entry of position `i` at ordinal `ord` (`left` to go), `x4` = the previous position's quartet `last`. -/
structure Base (s : MachineState) (p : Positions) : Prop where
  indices : s.getReg .x8=BitVec.ofNat 64 indicesBase
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  count : s.getReg .x18=8192
  leaves : s.getReg .x19=4194304
  start : s.getReg .x20=BitVec.ofNat 64 proofBase
  dest : s.getReg .x21=BitVec.ofNat 64 proofBase
  mark : s.getReg .x23=1
  slots : s.getReg .x24=BitVec.ofNat 64 groupSlots
  capLeaves : s.getReg .x27=256

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg mem_of_store open_zero

theorem reply_pc {bits : Nat} (s : MachineState) (dst : Word) (coins : BitVec bits) :
    (writeBits s dst coins).pc = s.pc + 4 := by simp only [writeBits,MachineState.setPC]

theorem plain_step (s : MachineState) (op : Instr) (yes : plain op=true) (free : memoryArgumentsValid s op=true) :
    ordinaryStep s (.base op)=some (execInstrBr s op) := (ord_iff s op yes).mpr free

theorem quarter (i : Index) : (BitVec.ofNat 64 i.val >>> (2:Nat))=BitVec.ofNat 64 (i.val/4) := by
  have : i.val<16777216 := i.isLt; rw [shift_right_nat _ _ (by omega)]; rfl

private theorem same_quartet (i : Index) (last : Nat) (small : last<2^64) :
    (BitVec.ofNat 64 (i.val/4) == BitVec.ofNat 64 last)=decide (i.val/4=last) := by
  have hi : i.val<16777216 := i.isLt
  by_cases h : i.val/4=last
  · simp [h]
  · have ne : BitVec.ofNat 64 (i.val/4)≠BitVec.ofNat 64 last := by
      intro e; have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (show i.val/4<2^64 by omega)] at this
      exact h this
    simp [h, ne]

theorem tile16' (i : Index) :
    (BitVec.ofNat 64 i.val <<< (4:Nat)) &&& 65535#64=BitVec.ofNat 64 (16*(i.val%4096)) := by
  have hi : i.val<16777216 := i.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i.val<2^64), show (65535:Nat)%2^64=2^16-1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
  norm_num
  omega

theorem entry_address' (e : Nat) :
    BitVec.ofNat 64 (16*e)+BitVec.ofNat 64 tableBase=wordAddress (tableWord e) := by
  rw [← BitVec.ofNat_add]; unfold wordAddress; congr 1; simp only [tableBase, tableWord]; omega

theorem block_value (i : Index) :
    ((BitVec.ofNat 64 (i.val/4)) <<< (10:Nat))+BitVec.ofNat 64 groupSlots=
      wordAddress (blockWord (i.val/4)) := by
  rw [shift_left_nat, ← BitVec.ofNat_add]
  unfold wordAddress blockWord groupSlots trapdoorBase LENGTH LOG_LENGTH
  congr 1; omega

theorem word_add (w c : Nat) (h : c%8=0) : wordAddress w+BitVec.ofNat 64 c=wordAddress (w+c/8) := by
  unfold wordAddress; rw [← BitVec.ofNat_add]; congr 1; omega

theorem even_addresses (g : Nat) (even : g%2=0) :
    replyWord g=blockWord g+21 ∧ rebuiltWord g=blockWord g+64 ∧ nodeWordOf (g^^^1)=blockWord g+17 := by
  obtain ⟨d,m⟩ := xor_one g
  unfold replyWord rebuiltWord nodeWordOf; rw [d,m]
  refine ⟨?_,rfl,?_⟩ <;> unfold blockWord <;> omega

theorem odd_addresses (g : Nat) (odd : g%2=1) :
    replyWord g=blockWord g-132 ∧ rebuiltWord g=blockWord g+64 ∧ nodeWordOf (g^^^1)=blockWord g-107 := by
  obtain ⟨d,m⟩ := xor_one g
  unfold replyWord rebuiltWord nodeWordOf; rw [d,m]
  refine ⟨?_,?_,?_⟩ <;> unfold blockWord <;> omega

/-- The entry's reply offset added to the quartet block (row 3088). -/
theorem reply_offset (i : Index) :
    (BitVec.ofNat 16 (tabR (i.val%4096))).signExtend 64+wordAddress (blockWord (i.val/4))=
      wordAddress (replyWord (i.val/4)) := by
  have hi : i.val<16777216 := i.isLt
  have par : (i.val%4096)/4%2=(i.val/4)%2 := by omega
  unfold tabR; rw [par]
  rcases Nat.mod_two_eq_zero_or_one (i.val/4) with h|h
  · rw [if_neg (by omega), (even_addresses _ h).1,
      show (BitVec.ofNat 16 168).signExtend 64=BitVec.ofNat 64 168 by decide]
    unfold wordAddress blockWord; rw [← BitVec.ofNat_add]; congr 1; omega
  · rw [if_pos h, (odd_addresses _ h).1,
      show (BitVec.ofNat 16 64480).signExtend 64=BitVec.ofNat 64 18446744073709550560 by decide]
    unfold wordAddress blockWord; rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- The entry's sibling-node offset added to the quartet block (row 3090). -/
theorem node_offset (i : Index) :
    (BitVec.ofNat 16 (tabG (i.val%4096))).signExtend 64+wordAddress (blockWord (i.val/4))=
      wordAddress (nodeWordOf (i.val/4^^^1)) := by
  have hi : i.val<16777216 := i.isLt
  have par : (i.val%4096)/4%2=(i.val/4)%2 := by omega
  unfold tabG; rw [par]
  rcases Nat.mod_two_eq_zero_or_one (i.val/4) with h|h
  · rw [if_neg (by omega), (even_addresses _ h).2.2,
      show (BitVec.ofNat 16 136).signExtend 64=BitVec.ofNat 64 136 by decide]
    unfold wordAddress blockWord; rw [← BitVec.ofNat_add]; congr 1; omega
  · rw [if_pos h, (odd_addresses _ h).2.2,
      show (BitVec.ofNat 16 64680).signExtend 64=BitVec.ofNat 64 18446744073709550760 by decide]
    unfold wordAddress blockWord; rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- Signed halfword `j` (2 or 3) of an entry's dword 0. -/
theorem entry_half (s : MachineState) (e : Nat) (he : e<4096) (tab : TableAt s) :
    (s.getHalfword (wordAddress (tableWord e)+signExtend12 4#12)).signExtend 64=
        (BitVec.ofNat 16 (tabR e)).signExtend 64 ∧
      (s.getHalfword (wordAddress (tableWord e)+signExtend12 6#12)).signExtend 64=
        (BitVec.ofNat 16 (tabG e)).signExtend 64 := by
  have fit : 8*tableWord e+8 ≤ 2^64 := by simp only [tableWord]; omega
  have w0 := tab e he 0 (by decide)
  rw [Nat.add_zero] at w0
  have low : tabEntry e 0=tabT e+65536*tabS e+4294967296*tabR e+281474976710656*tabG e := by simp [tabEntry]
  constructor
  · rw [show wordAddress (tableWord e)+signExtend12 4#12=BitVec.ofNat 64 (8*tableWord e+2*2) by
      rw [show signExtend12 4#12=BitVec.ofNat 64 4 by decide]; unfold wordAddress; rw [← BitVec.ofNat_add],
      table_half s _ 2 fit (by decide)]
    change ((memoryView s (tableWord e) >>> (2*16)).truncate 16).signExtend 64=_
    rw [w0, low, half2 _ _ _ _ (tab_t_lt _) (tab_s_lt _) (tab_r_lt _) (tab_g_lt _)]
  · rw [show wordAddress (tableWord e)+signExtend12 6#12=BitVec.ofNat 64 (8*tableWord e+2*3) by
      rw [show signExtend12 6#12=BitVec.ofNat 64 6 by decide]; unfold wordAddress; rw [← BitVec.ofNat_add],
      table_half s _ 3 fit (by decide)]
    change ((memoryView s (tableWord e) >>> (3*16)).truncate 16).signExtend 64=_
    rw [w0, low, half3 _ _ _ _ (tab_t_lt _) (tab_s_lt _) (tab_r_lt _) (tab_g_lt _)]

theorem half_setPC' (s : MachineState) (p a : Word) : (s.setPC p).getHalfword a=s.getHalfword a := rfl
theorem half_setReg' (s : MachineState) (r : Reg) (v a : Word) : (s.setReg r v).getHalfword a=s.getHalfword a := by
  cases r <;> rfl

/-- The parity flag (kept for the downstream names; the head no longer branches on it). -/
def oddOf (i : Index) : Bool := decide (i.val/4%2=1)

/-- The word after the rebuilt block of quartet `q` (`B_q + 712`): the address of its level-22 sibling node. -/
abbrev pointerWord (q : Nat) := rebuiltWord q+25

theorem pointer_word_eq (q : Nat) : wordAddress (blockWord q)+signExtend12 712#12=wordAddress (pointerWord q) := by
  rw [show signExtend12 712#12=BitVec.ofNat 64 712 by decide, word_add _ _ (by decide)]
  unfold pointerWord rebuiltWord; rfl

/-- The writer's pointer address (`GroupOpenMemory.pointerAddress`) is the pointer word of the quartet. -/
theorem pointer_address_word (i : Nat) : BitVec.ofNat 64 (pointerAddress i)=wordAddress (pointerWord (i/4)) := by
  unfold pointerAddress pointerWord rebuiltWord blockWord wordAddress groupSlots trapdoorBase LENGTH LOG_LENGTH
  congr 1; omega

/-- The writer's level-0 source (`GroupOpenMemory.quadAddress`) is the commit's node of the sibling quartet. -/
theorem quad_address_node (i : Nat) : quadAddress i=8*nodeWordOf (i/4^^^1) := by
  obtain ⟨d,m⟩ := xor_one (i/4)
  have r : i/4%2<2 := Nat.mod_lt _ (by decide)
  unfold quadAddress nodeWordOf blockWord groupSlots trapdoorBase LENGTH LOG_LENGTH
  rw [d,m]
  omega

end TwoPermutationPrototype.GroupedOpening
