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

structure Input (s : MachineState) (i : Index) (ord left last : Nat) extends Registers s ord left where
  pc : s.pc=address 3077
  one : s.getReg .x23=1
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  leaves : s.getReg .x19=4194304
  slots : s.getReg .x24=BitVec.ofNat 64 groupSlots
  quartet : s.getReg .x4=BitVec.ofNat 64 last
  small : last<2^64
  loaded : s.getMem (indexAt ord)=BitVec.ofNat 64 i.val
  access : accessValid (indexAt ord) 8=true
  /-- The table base (the ABI's `sp`) and the entry mask set once by the header (row 732). -/
  sp : s.getReg .x2=BitVec.ofNat 64 tableBase
  mask : s.getReg .x1=65535
  /-- The embedded table is in place. -/
  table : TableAt s

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg mem_of_store open_zero

theorem reply_pc {bits : Nat} (s : MachineState) (dst : Word) (coins : BitVec bits) :
    (writeBits s dst coins).pc = s.pc + 4 := by simp only [writeBits,MachineState.setPC]

private theorem load_ok (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last) :
    memoryArgumentsValid s (.LD .x6 .x14 0)=true := by
  simpa [memoryArgumentsValid,memAccess,r.index,show signExtend12 0#12=0#64 by decide] using r.access

theorem plain_step (s : MachineState) (op : Instr) (yes : plain op=true) (free : memoryArgumentsValid s op=true) :
    ordinaryStep s (.base op)=some (execInstrBr s op) := (ord_iff s op yes).mpr free

private theorem quarter (i : Index) : (BitVec.ofNat 64 i.val >>> (2:Nat))=BitVec.ofNat 64 (i.val/4) := by
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

/-! ### Head rows 3077..3096 -/

/-- The five unconditional head rows 3077..3081: the index, its quartet, `16 i` and the table entry. -/
def headA : List Row := [(3077,.LD .x6 .x14 0),(3078,.SRLI .x28 .x6 2),(3079,.SLLI .x3 .x6 4),
  (3080,.AND .x30 .x3 .x1),(3081,.ADD .x30 .x30 .x2)]
theorem head_split : headRows=headA++[(3082,.BEQ .x28 .x4 56)] := rfl

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

private theorem head_entry (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last) :
    let t:=walkRows s headA
    legal headA s ∧ t.pc=address 3082 ∧ t.mem=s.mem ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      t.getReg .x28=BitVec.ofNat 64 (i.val/4) ∧ t.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) ∧
      t.getReg .x30=wordAddress (tableWord (i.val%4096)) ∧
      (∀ k, k≠.x6 → k≠.x28 → k≠.x3 → k≠.x30 → t.getReg k=s.getReg k) := by
  have ld := load_ok s i ord left last r
  have q := quarter i
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · show legal ((3077,.LD .x6 .x14 0)::[(3078,.SRLI .x28 .x6 2),(3079,.SLLI .x3 .x6 4),
      (3080,.AND .x30 .x3 .x1),(3081,.ADD .x30 .x30 .x2)]) s
    exact ⟨r.pc,plain_step _ _ rfl ld,legal_of_chain _ _ (by decide) (by simp [pcChain,execInstrBr,r.pc,address])⟩
  · simp [headA,walkRows,execInstrBr,r.pc,address]
  · simp [headA,walkRows,execInstrBr]
  · simp [headA,walkRows,execInstrBr,r.index,r.loaded,show signExtend12 0#12=0#64 by decide]
  · simp [headA,walkRows,execInstrBr,r.index,r.loaded,show signExtend12 0#12=0#64 by decide,q]
  · simp [headA,walkRows,execInstrBr,r.index,r.loaded,show signExtend12 0#12=0#64 by decide]
  · simp only [headA,walkRows,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
      Opening.getReg_setReg,r.mask,r.sp]
    simp [r.index,r.loaded,show signExtend12 0#12=0#64 by decide]
    rw [tile16' i, entry_address']
  · intro k a b c d; simp [headA,walkRows,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d]

/-- Rows 3077..3082 when the quartet repeats: on to row 3096. -/
theorem head_skip0 (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (same : i.val/4=last) :
    let t:=walkRows s headRows
    legal headRows s ∧ t.pc=address 3096 ∧ t.mem=s.mem ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      t.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) ∧ t.getReg .x30=wordAddress (tableWord (i.val%4096)) ∧
      (∀ k, k≠.x6 → k≠.x28 → k≠.x3 → k≠.x30 → t.getReg k=s.getReg k) := by
  obtain ⟨l0,pc0,mem0,x6,x28,x3,x30,keep0⟩ := head_entry s i ord left last r
  have eq := same_quartet i last r.small
  rw [same] at eq; simp only [decide_true] at eq
  set a:=walkRows s headA with ha
  have taken : execInstrBr a (.BEQ .x28 .x4 56)=a.setPC (address 3096) := by
    have yes : (a.getReg .x28 == a.getReg .x4)=true := by
      rw [x28, keep0 _ (by decide) (by decide) (by decide) (by decide), r.quartet, same]; simp
    simp only [execInstrBr,yes,ite_true,pc0]
    exact congrArg a.setPC (by decide : address 3082+signExtend13 56=address 3096)
  have split : walkRows s headRows=execInstrBr a (.BEQ .x28 .x4 56) := by
    rw [head_split, walk_join]; rfl
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [head_split]; exact legal_append _ _ _ l0 ⟨pc0,plain_step _ _ rfl (no_mem_valid _ _ rfl),trivial⟩
  · rw [split, taken]; rfl
  · rw [split, taken]; exact mem0
  · rw [split, taken, MachineState.getReg_setPC]; exact x6
  · rw [split, taken, MachineState.getReg_setPC]; exact x3
  · rw [split, taken, MachineState.getReg_setPC]; exact x30
  · intro k a b c d; rw [split, taken, MachineState.getReg_setPC]; exact keep0 k a b c d

/-- Row 3096: `addi x10,x0,1024`. -/
theorem load_row (u : MachineState) (pc : u.pc=address 3096) :
    let v:=walkRows u loadRow
    legal loadRow u ∧ v.pc=address 3097 ∧ v.mem=u.mem ∧ v.getReg .x10=1024 ∧
      (∀ k, k≠.x10 → v.getReg k=u.getReg k) := by
  refine ⟨legal_of_chain _ _ (by decide) (by simp [loadRow,pcChain,execInstrBr,pc,address]),?_,?_,?_,?_⟩
  all_goals simp [loadRow,walkRows,execInstrBr,pc,address,show signExtend12 1024#12=1024#64 by decide]
  all_goals first | (intro k a; simp [Ne.symm a]) | rfl

/-- The skip path: rows 3077..3082, then row 3096 (`x10 := 1024`), on to row 3097. -/
theorem head_skip (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (same : i.val/4=last) :
    let t:=walkRows s skipRows
    legal skipRows s ∧ t.pc=address 3097 ∧ t.mem=s.mem ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      t.getReg .x10=1024 ∧ t.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) ∧
      t.getReg .x30=wordAddress (tableWord (i.val%4096)) ∧
      (∀ k, k≠.x6 → k≠.x28 → k≠.x10 → k≠.x3 → k≠.x30 → t.getReg k=s.getReg k) := by
  obtain ⟨l0,pc0,mem0,x60,x30',x300,keep0⟩ := head_skip0 s i ord left last r same
  obtain ⟨l1,pc1,mem1,x101,keep1⟩ := load_row (walkRows s headRows) pc0
  have split : walkRows s skipRows=walkRows (walkRows s headRows) loadRow := walk_join _ _ _
  refine ⟨legal_append _ _ _ l0 l1,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [split]; exact pc1
  · rw [split, mem1]; exact mem0
  · rw [split, keep1 _ (by decide)]; exact x60
  · rw [split]; exact x101
  · rw [split, keep1 _ (by decide)]; exact x30'
  · rw [split, keep1 _ (by decide)]; exact x300
  · intro k h6 h28 h10 h3 h30; rw [split, keep1 k h10]; exact keep0 k h6 h28 h3 h30

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

private def aluRows : List Row := [(3083,.ADDI .x4 .x28 0),(3084,.SLLI .x7 .x28 10),
  (3085,.ADD .x7 .x7 .x24),(3086,.ADDI .x12 .x7 512)]
private def selRows : List Row := [(3087,.LH .x10 .x30 4),(3088,.ADD .x10 .x10 .x7),(3089,.LH .x31 .x30 6),
  (3090,.ADD .x31 .x31 .x7),(3091,.ADDI .x13 .x0 2)]
private theorem new_split : newRows=aluRows++selRows := rfl

theorem half_setPC' (s : MachineState) (p a : Word) : (s.setPC p).getHalfword a=s.getHalfword a := rfl
theorem half_setReg' (s : MachineState) (r : Reg) (v a : Word) : (s.setReg r v).getHalfword a=s.getHalfword a := by
  cases r <;> rfl

/-- A new quartet before its inverse call: rows 3077..3091 (`x10` = its reply, `x12` = its rebuilt block,
`x13 = 2`, `x31` = the address of the sibling group's node, `x7` = its block). -/
theorem head_pre (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (fresh : i.val/4≠last) :
    let t:=walkRows s preRows
    legal preRows s ∧ t.pc=address 3092 ∧ t.mem=s.mem ∧
      t.getReg .x10=wordAddress (replyWord (i.val/4)) ∧ t.getReg .x12=wordAddress (rebuiltWord (i.val/4)) ∧
      t.getReg .x13=2 ∧ t.getReg .x31=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      t.getReg .x6=BitVec.ofNat 64 i.val ∧ t.getReg .x28=BitVec.ofNat 64 (i.val/4) ∧
      t.getReg .x4=BitVec.ofNat 64 (i.val/4) ∧ t.getReg .x7=wordAddress (blockWord (i.val/4)) ∧
      t.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) ∧ t.getReg .x30=wordAddress (tableWord (i.val%4096)) ∧
      (∀ k, k≠.x4 → k≠.x6 → k≠.x7 → k≠.x10 → k≠.x12 → k≠.x13 → k≠.x28 → k≠.x30 → k≠.x31 → k≠.x3 →
        t.getReg k=s.getReg k) := by
  have hi : i.val<16777216 := i.isLt
  have he : i.val%4096<4096 := Nat.mod_lt _ (by decide)
  obtain ⟨l0,pc0,mem0,x6,x28,x3,x30,keep0⟩ := head_entry s i ord left last r
  have eq := same_quartet i last r.small
  simp only [fresh, decide_false] at eq
  have ne : BitVec.ofNat 64 (i.val/4)≠BitVec.ofNat 64 last := by
    intro e; have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt r.small,Nat.mod_eq_of_lt (show i.val/4<2^64 by omega)] at this
    exact fresh this
  set a:=walkRows s headA with ha
  have fall : execInstrBr a (.BEQ .x28 .x4 56)=a.setPC (address 3083) := by
    have no : (a.getReg .x28 == a.getReg .x4)=false := by
      rw [x28, keep0 _ (by decide) (by decide) (by decide) (by decide), r.quartet]; simp [ne]
    simp only [execInstrBr,no,Bool.false_eq_true,ite_false,pc0]
    exact congrArg a.setPC (by decide : address 3082+4=address 3083)
  set b:=a.setPC (address 3083) with hb
  have bk (k : Reg) : b.getReg k=a.getReg k := MachineState.getReg_setPC ..
  -- rows 3083..3086
  set c:=walkRows b aluRows with hc
  have cpc : c.pc=address 3087 := by simp [hc,aluRows,walkRows,execInstrBr,hb,address]
  have cmem : c.mem=s.mem := by simp [hc,aluRows,walkRows,execInstrBr,hb]; exact mem0
  have c7 : c.getReg .x7=wordAddress (blockWord (i.val/4)) := by
    simp [hc,aluRows,walkRows,execInstrBr]
    rw [bk, bk, x28, keep0 _ (by decide) (by decide) (by decide) (by decide), r.slots]; exact block_value i
  have c12 : c.getReg .x12=wordAddress (rebuiltWord (i.val/4)) := by
    simp [hc,aluRows,walkRows,execInstrBr]
    rw [bk, bk, x28, keep0 _ (by decide) (by decide) (by decide) (by decide), r.slots, block_value i,
      show signExtend12 512#12=BitVec.ofNat 64 512 by decide, word_add _ _ (by decide)]
    rfl
  have c4 : c.getReg .x4=BitVec.ofNat 64 (i.val/4) := by
    simp [hc,aluRows,walkRows,execInstrBr,show signExtend12 0#12=0#64 by decide]; rw [bk, x28]
  have ckeep (k : Reg) (h4 : k≠.x4) (h7 : k≠.x7) (h12 : k≠.x12) : c.getReg k=b.getReg k := by
    simp [hc,aluRows,walkRows,execInstrBr,Ne.symm h4,Ne.symm h7,Ne.symm h12]
  have cl : legal aluRows b := legal_of_chain _ _ (by decide) (by simp [aluRows,pcChain,execInstrBr,hb,address])
  -- rows 3087..3091
  have ctab : TableAt c := by
    intro e' he' h' hh'
    have : memoryView c (tableWord e'+h')=memoryView s (tableWord e'+h') := by
      unfold memoryView MachineState.getMem; rw [cmem]
    rw [this]; exact r.table e' he' h' hh'
  have c30 : c.getReg .x30=wordAddress (tableWord (i.val%4096)) := by
    rw [ckeep _ (by decide) (by decide) (by decide), bk]; exact x30
  obtain ⟨hR,hG⟩ := entry_half c _ he ctab
  have fit : 8*tableWord (i.val%4096)+8 ≤ 2^36 := by simp only [tableWord]; omega
  have v4 : accessValid (wordAddress (tableWord (i.val%4096))+signExtend12 4#12) 2=true := by
    rw [show signExtend12 4#12=BitVec.ofNat 64 4 by decide]; unfold wordAddress; rw [← BitVec.ofNat_add]
    exact table_access _ 2 (by omega) (by omega)
  have v6 : accessValid (wordAddress (tableWord (i.val%4096))+signExtend12 6#12) 2=true := by
    rw [show signExtend12 6#12=BitVec.ofNat 64 6 by decide]; unfold wordAddress; rw [← BitVec.ofNat_add]
    exact table_access _ 2 (by omega) (by omega)
  set d:=walkRows c selRows with hd
  have dl : legal selRows c := by
    simp [selRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,cpc,c30,v4,v6,address]
  have dpc : d.pc=address 3092 := by simp [hd,selRows,walkRows,execInstrBr,cpc,address]
  have dmem : d.mem=c.mem := by simp [hd,selRows,walkRows,execInstrBr]
  have d10 : d.getReg .x10=wordAddress (replyWord (i.val/4)) := by
    have e1 : d.getReg .x10=(c.getHalfword (c.getReg .x30+signExtend12 4#12)).signExtend 64+c.getReg .x7 := rfl
    rw [e1, c30, hR, c7]; exact reply_offset i
  have d31 : d.getReg .x31=wordAddress (nodeWordOf (i.val/4^^^1)) := by
    have e1 : d.getReg .x31=(c.getHalfword (c.getReg .x30+signExtend12 6#12)).signExtend 64+c.getReg .x7 := rfl
    rw [e1, c30, hG, c7]; exact node_offset i
  have d13 : d.getReg .x13=2 := by simp [hd,selRows,walkRows,execInstrBr,show signExtend12 2#12=2#64 by decide]
  have dkeep (k : Reg) (h10 : k≠.x10) (h31 : k≠.x31) (h13 : k≠.x13) : d.getReg k=c.getReg k := by
    simp [hd,selRows,walkRows,execInstrBr,Ne.symm h10,Ne.symm h31,Ne.symm h13]
  have at_t : walkRows s preRows=d := by
    show walkRows s (headA++[(3082,.BEQ .x28 .x4 56)]++(aluRows++selRows))=d
    rw [walk_join, walk_join, walk_join]
    show walkRows (walkRows (execInstrBr a (.BEQ .x28 .x4 56)) aluRows) selRows=d
    rw [fall]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · show legal (headA++[(3082,.BEQ .x28 .x4 56)]++(aluRows++selRows)) s
    refine legal_append _ _ _ (legal_append _ _ _ l0 ⟨pc0,plain_step _ _ rfl (no_mem_valid _ _ rfl),trivial⟩) ?_
    rw [walk_join]
    show legal (aluRows++selRows) (execInstrBr a (.BEQ .x28 .x4 56))
    rw [fall]; exact legal_append _ _ _ cl dl
  · rw [at_t]; exact dpc
  · rw [at_t, dmem]; exact cmem
  · rw [at_t]; exact d10
  · rw [at_t, dkeep _ (by decide) (by decide) (by decide)]; exact c12
  · rw [at_t]; exact d13
  · rw [at_t]; exact d31
  · rw [at_t, dkeep _ (by decide) (by decide) (by decide), ckeep _ (by decide) (by decide) (by decide), bk]; exact x6
  · rw [at_t, dkeep _ (by decide) (by decide) (by decide), ckeep _ (by decide) (by decide) (by decide), bk]; exact x28
  · rw [at_t, dkeep _ (by decide) (by decide) (by decide)]; exact c4
  · rw [at_t, dkeep _ (by decide) (by decide) (by decide)]; exact c7
  · rw [at_t, dkeep _ (by decide) (by decide) (by decide), ckeep _ (by decide) (by decide) (by decide), bk]; exact x3
  · rw [at_t, dkeep _ (by decide) (by decide) (by decide)]; exact c30
  · intro k h4 h6 h7 h10 h12 h13 h28 h30 h31 h3
    rw [at_t, dkeep k h10 h31 h13, ckeep k h4 h7 h12, bk]; exact keep0 k h6 h28 h3 h30

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

/-- Row 775: `sd x30, 712(x7)` stores the sibling node's address in the pointer word. -/
theorem ptr_row (u : MachineState) (q : Nat) (hq : q<4194304) (pc : u.pc=address 3095)
    (b7 : u.getReg .x7=wordAddress (blockWord q)) :
    let v:=walkRows u ptrRows
    legal ptrRows u ∧ v.pc=address 3096 ∧ (∀ k, v.getReg k=u.getReg k) ∧
      (∀ w, w<2^33 → memoryView v w=writeWord (memoryView u) (pointerWord q) (u.getReg .x31) w) := by
  have ad : u.getReg .x7+signExtend12 712#12=wordAddress (pointerWord q) := by rw [b7]; exact pointer_word_eq q
  have room : pointerWord q<2^33 := by unfold pointerWord rebuiltWord blockWord; omega
  have ok : accessValid (wordAddress (pointerWord q)) 8=true :=
    Opening.aligned_access (8*pointerWord q) (by omega) (by unfold MEMORY_BYTES; omega)
  have smem : (walkRows u ptrRows).mem=(u.setMem (wordAddress (pointerWord q)) (u.getReg .x31)).mem := by
    simp [ptrRows,walkRows,execInstrBr,ad]
  refine ⟨⟨pc,?_,trivial⟩,?_,?_,?_⟩
  · simp [ordinaryStep,memoryArgumentsValid,memAccess,ad,ok]
  · simp [ptrRows,walkRows,execInstrBr,pc,address]
  · intro k; simp [ptrRows,walkRows,execInstrBr]
  · intro w hw
    change (walkRows u ptrRows).mem (wordAddress w)=_
    rw [smem]
    exact memory_at_store (state:=u) (address:=pointerWord q) (index:=w) (value:=u.getReg .x31) (by omega) (by omega)

/-- A new quartet after its inverse reply landed in the rebuilt block: rows 3093..3096 (`x13 := 1`,
`x12 := 1536`, the sibling group's node address to the pointer word, `x10 := 1024`). -/
theorem head_post (a : MachineState) (i : Index) (pc : a.pc=address 3093)
    (b7 : a.getReg .x7=wordAddress (blockWord (i.val/4))) :
    let t:=walkRows a headPost
    legal headPost a ∧ t.pc=address 3097 ∧ t.getReg .x10=1024 ∧ t.getReg .x12=1536 ∧ t.getReg .x13=1 ∧
      (∀ k, k≠.x10 → k≠.x12 → k≠.x13 → t.getReg k=a.getReg k) ∧
      (∀ w, w<2^33 → memoryView t w=writeWord (memoryView a) (pointerWord (i.val/4)) (a.getReg .x31) w) := by
  have hi : i.val<16777216 := i.isLt
  set u:=walkRows a restoreRows with hu
  have ul : legal restoreRows a ∧ u.pc=address 3095 ∧ u.mem=a.mem ∧ u.getReg .x12=1536 ∧
      u.getReg .x13=1 ∧ (∀ k, k≠.x12 → k≠.x13 → u.getReg k=a.getReg k) := by
    refine ⟨legal_of_chain _ _ (by decide) (by simp [restoreRows,pcChain,execInstrBr,pc,address]),?_,?_,?_,?_,?_⟩
    all_goals simp [hu,restoreRows,walkRows,execInstrBr,pc,address,
      show signExtend12 1536#12=1536#64 by decide,
      show signExtend12 1#12=1#64 by decide]
    all_goals first | (intro k a b; simp [Ne.symm a,Ne.symm b]) | rfl
  obtain ⟨ul1,upc,umem,u12,u13,ukeep⟩ := ul
  obtain ⟨sl,spc,skeep,sview⟩ := ptr_row u (i.val/4) (by omega) upc ((ukeep _ (by decide) (by decide)).trans b7)
  set v:=walkRows u ptrRows with hv
  obtain ⟨ll,lpc,lmem,l10,lkeep⟩ := load_row v spc
  have split : headPost=restoreRows++ptrRows++loadRow := rfl
  have at_t : walkRows a headPost=walkRows v loadRow := by rw [split, walk_join, walk_join]
  have view (w : Nat) : memoryView u w=memoryView a w := by unfold memoryView MachineState.getMem; rw [umem]
  have lview (w : Nat) : memoryView (walkRows v loadRow) w=memoryView v w := by
    unfold memoryView MachineState.getMem; rw [lmem]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [split]; exact legal_append _ _ _ (legal_append _ _ _ ul1 sl) (by rw [walk_join]; exact ll)
  · rw [at_t]; exact lpc
  · rw [at_t]; exact l10
  · rw [at_t, lkeep _ (by decide), skeep]; exact u12
  · rw [at_t, lkeep _ (by decide), skeep]; exact u13
  · intro k h10 h12 h13
    rw [at_t, lkeep k h10, skeep k]; exact ukeep k h12 h13
  · intro w hw
    rw [at_t, lview w, sview w hw, ukeep _ (by decide) (by decide)]
    simp only [writeWord]
    split
    · rfl
    · exact view w

end TwoPermutationPrototype.GroupedOpening
