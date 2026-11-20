import CommitGolfCandidate.K3OpenCopy
import CommitGolfCandidate.K3OpenCall
import CommitGolfCandidate.K1OpenSalt
import CommitGolfCandidate.GroupOpenMemory

/-! K3-lite prefix, one position: addresses, entry registers and the head paths (rows 740..751, 769..776). -/
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
  divReg : s.getReg .x29=11

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
  pc : s.pc=address 740
  one : s.getReg .x23=1
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  leaves : s.getReg .x19=4194304
  slots : s.getReg .x24=BitVec.ofNat 64 groupSlots
  quartet : s.getReg .x4=BitVec.ofNat 64 last
  small : last<2^64
  loaded : s.getMem (indexAt ord)=BitVec.ofNat 64 i.val
  access : accessValid (indexAt ord) 8=true
  /-- The salt-chain constants set once by the header (rows 755, 756). -/
  gp : s.getReg .x3=374
  sp : s.getReg .x2=4352
  mask : s.getReg .x1=4095
  linkBase : s.getReg .x18=8192

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

/-- Rows 740..742 when the quartet repeats: nothing but `x6`, `x28`, then on to row 776. -/
theorem head_skip0 (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (same : i.val/4=last) :
    let t:=walkRows s headRows
    legal headRows s ∧ t.pc=address 776 ∧ t.mem=s.mem ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      (∀ k, k≠.x6 → k≠.x28 → t.getReg k=s.getReg k) := by
  have ld := load_ok s i ord left last r
  have eq := same_quartet i last r.small
  rw [same] at eq; simp only [decide_true] at eq
  have q := quarter i
  rw [same] at q
  refine ⟨?_,?_,?_,?_,?_⟩
  · show legal ((740,.LD .x6 .x14 0)::[(741,.SRLI .x28 .x6 2),(742,.BEQ .x28 .x4 136)]) s
    exact ⟨r.pc,plain_step _ _ rfl ld,legal_of_chain _ _ (by decide) (by simp [pcChain,execInstrBr,r.pc,address])⟩
  all_goals simp [headRows,walkRows,execInstrBr,r.pc,r.index,r.loaded,r.quartet,address,
    q,eq,show signExtend12 0#12=0#64 by decide,show signExtend13 136#13=136#64 by decide]
  all_goals first | (intro k a b; simp [Ne.symm a,Ne.symm b]) | rfl

/-- Row 776: `addi x10,x0,1024`. -/
theorem load_row (u : MachineState) (pc : u.pc=address 776) :
    let v:=walkRows u loadRow
    legal loadRow u ∧ v.pc=address 777 ∧ v.mem=u.mem ∧ v.getReg .x10=1024 ∧
      (∀ k, k≠.x10 → v.getReg k=u.getReg k) := by
  refine ⟨legal_of_chain _ _ (by decide) (by simp [loadRow,pcChain,execInstrBr,pc,address]),?_,?_,?_,?_⟩
  all_goals simp [loadRow,walkRows,execInstrBr,pc,address,show signExtend12 1024#12=1024#64 by decide]
  all_goals first | (intro k a; simp [Ne.symm a]) | rfl

/-- The skip path: rows 740..742, then row 776 (`x10 := 1024`), on to row 777. -/
theorem head_skip (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (same : i.val/4=last) :
    let t:=walkRows s skipRows
    legal skipRows s ∧ t.pc=address 777 ∧ t.mem=s.mem ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      t.getReg .x10=1024 ∧ (∀ k, k≠.x6 → k≠.x28 → k≠.x10 → t.getReg k=s.getReg k) := by
  obtain ⟨l0,pc0,mem0,x60,keep0⟩ := head_skip0 s i ord left last r same
  obtain ⟨l1,pc1,mem1,x101,keep1⟩ := load_row (walkRows s headRows) pc0
  have split : walkRows s skipRows=walkRows (walkRows s headRows) loadRow := walk_join _ _ _
  refine ⟨legal_append _ _ _ l0 l1,?_,?_,?_,?_,?_⟩
  · rw [split]; exact pc1
  · rw [split, mem1]; exact mem0
  · rw [split, keep1 _ (by decide)]; exact x60
  · rw [split]; exact x101
  · intro k h6 h28 h10; rw [split, keep1 k h10]; exact keep0 k h6 h28

theorem block_value (i : Index) :
    ((BitVec.ofNat 64 (i.val/4)) <<< (10:Nat))+BitVec.ofNat 64 groupSlots=
      wordAddress (blockWord (i.val/4)) := by
  rw [shift_left_nat, ← BitVec.ofNat_add]
  unfold wordAddress blockWord groupSlots trapdoorBase LENGTH LOG_LENGTH
  congr 1; omega

theorem word_add (w c : Nat) (h : c%8=0) : wordAddress w+BitVec.ofNat 64 c=wordAddress (w+c/8) := by
  unfold wordAddress; rw [← BitVec.ofNat_add]; congr 1; omega

/-- Rows 740..748 of a new quartet (`x4 := q`), up to the parity branch at 748. -/
private def newPart : List Row := headRows ++ newRows
private def aluRows : List Row := [(743,.ADDI .x4 .x28 0),(744,.SLLI .x7 .x28 10),
  (745,.ADD .x7 .x7 .x24),(746,.ADDI .x12 .x7 512),(747,.ANDI .x30 .x6 4)]

private theorem new_head (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (fresh : i.val/4≠last) :
    let t:=walkRows s headRows
    legal headRows s ∧ t.pc=address 743 ∧ t.mem=s.mem ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      t.getReg .x28=BitVec.ofNat 64 (i.val/4) ∧ (∀ k, k≠.x6 → k≠.x28 → t.getReg k=s.getReg k) := by
  have ld := load_ok s i ord left last r
  have eq := same_quartet i last r.small
  simp only [fresh, decide_false] at eq
  have q := quarter i
  have hi : i.val<16777216 := i.isLt
  have ne : BitVec.ofNat 64 (i.val/4)≠BitVec.ofNat 64 last := by
    intro e; have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt r.small,Nat.mod_eq_of_lt (show i.val/4<2^64 by omega)] at this
    exact fresh this
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · show legal ((740,.LD .x6 .x14 0)::[(741,.SRLI .x28 .x6 2),(742,.BEQ .x28 .x4 136)]) s
    exact ⟨r.pc,plain_step _ _ rfl ld,legal_of_chain _ _ (by decide) (by simp [pcChain,execInstrBr,r.pc,address])⟩
  all_goals simp [headRows,walkRows,execInstrBr,r.pc,r.index,r.loaded,r.quartet,address,
    q,eq,ne,show signExtend12 0#12=0#64 by decide]
  all_goals first | (intro k a b; simp [Ne.symm a,Ne.symm b]) | rfl

private theorem alu_part (u : MachineState) (pc : u.pc=address 743) :
    let v:=walkRows u aluRows
    legal aluRows u ∧ v.pc=address 748 ∧ v.mem=u.mem ∧ v.getReg .x4=u.getReg .x28 ∧
      v.getReg .x7=(u.getReg .x28 <<< (10:Nat))+u.getReg .x24 ∧
      v.getReg .x12=((u.getReg .x28 <<< (10:Nat))+u.getReg .x24)+signExtend12 512#12 ∧
      v.getReg .x30=(u.getReg .x6 &&& signExtend12 4#12) ∧
      (∀ k, k≠.x4 → k≠.x7 → k≠.x12 → k≠.x30 → v.getReg k=u.getReg k) := by
  refine ⟨legal_of_chain _ _ (by decide) (by simp [aluRows,pcChain,execInstrBr,pc,address]),?_,?_,?_,?_,?_,?_,?_⟩
  · simp [aluRows,walkRows,execInstrBr,pc,address]
  · simp [aluRows,walkRows,execInstrBr]
  · simp [aluRows,walkRows,execInstrBr,show signExtend12 0#12=0#64 by decide]
  · simp [aluRows,walkRows,execInstrBr]
  · simp [aluRows,walkRows,execInstrBr]
  · simp [aluRows,walkRows,execInstrBr]
  · intro k a b c d; simp [aluRows,walkRows,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d]

private theorem new_part (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (fresh : i.val/4≠last) :
    let t:=walkRows s newPart
    legal newPart s ∧ t.pc=(if i.val/4%2=1 then address 769 else address 749) ∧ t.mem=s.mem ∧
      t.getReg .x6=BitVec.ofNat 64 i.val ∧ t.getReg .x28=BitVec.ofNat 64 (i.val/4) ∧
      t.getReg .x4=BitVec.ofNat 64 (i.val/4) ∧ t.getReg .x7=wordAddress (blockWord (i.val/4)) ∧
      t.getReg .x12=wordAddress (rebuiltWord (i.val/4)) ∧
      (∀ k, k≠.x4 → k≠.x6 → k≠.x7 → k≠.x12 → k≠.x28 → k≠.x30 → t.getReg k=s.getReg k) := by
  obtain ⟨hl,hpc,hmem,h6,h28,hkeep⟩ := new_head s i ord left last r fresh
  set u:=walkRows s headRows with hu
  obtain ⟨al,apc,amem,a4,a7,a12,a30,akeep⟩ := alu_part u hpc
  set v:=walkRows u aluRows with hv
  have v6 : v.getReg .x6=BitVec.ofNat 64 i.val := (akeep _ (by decide) (by decide) (by decide) (by decide)).trans h6
  have v28 : v.getReg .x28=BitVec.ofNat 64 (i.val/4) := (akeep _ (by decide) (by decide) (by decide) (by decide)).trans h28
  have v7 : v.getReg .x7=wordAddress (blockWord (i.val/4)) := by
    rw [a7,h28,hkeep _ (by decide) (by decide),r.slots]; exact block_value i
  have v12 : v.getReg .x12=wordAddress (rebuiltWord (i.val/4)) := by
    rw [a12, ← a7, v7, show signExtend12 512#12=BitVec.ofNat 64 512 by decide,
      word_add _ _ (by decide)]
    rfl
  have v30 : v.getReg .x30=BitVec.ofNat 64 (4*(i.val/4%2)) := by rw [a30,h6]; exact and_four i.val
  let br : List Row := [(748,.BNE .x30 .x0 84)]
  have taken (nz : v.getReg .x30≠0#64) : execInstrBr v (.BNE .x30 .x0 84)=v.setPC (address 769) := by
    have yes : (v.getReg .x30 != v.getReg .x0)=true := by simp [open_zero,nz]
    simp only [execInstrBr,yes,ite_true,apc]
    exact congrArg v.setPC (by decide : address 748+signExtend13 84=address 769)
  have fall (z : v.getReg .x30=0#64) : execInstrBr v (.BNE .x30 .x0 84)=v.setPC (address 749) := by
    simp only [execInstrBr,open_zero,z,beq_self_eq_true,ite_true,apc]
    exact congrArg v.setPC (by decide : address 748+4=address 749)
  have bl : legal br v ∧ (walkRows v br).pc=(if i.val/4%2=1 then address 769 else address 749) ∧
      (walkRows v br).mem=v.mem ∧ (∀ k, (walkRows v br).getReg k=v.getReg k) := by
    refine ⟨⟨apc,plain_step _ _ rfl (no_mem_valid _ _ rfl),trivial⟩,?_,?_,?_⟩
    · show (execInstrBr v (.BNE .x30 .x0 84)).pc=_
      rcases Nat.mod_two_eq_zero_or_one (i.val/4) with h|h
      · rw [fall (by rw [v30,h]), if_neg (by omega)]; rfl
      · rw [taken (by rw [v30,h]; decide), if_pos h]; rfl
    · exact bne_mem' v _ _ _
    · intro k; exact bne_reg' v _ _ _ _
  have split : newPart=headRows++aluRows++br := rfl
  have at_t : walkRows s newPart=walkRows v br := by rw [split,walk_join,walk_join]
  obtain ⟨bl1,bpc,bmem,bkeep⟩ := bl
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [split]; exact legal_append _ _ _ (legal_append _ _ _ hl al) bl1
  · rw [at_t]; exact bpc
  · rw [at_t,bmem,amem,hmem]
  · rw [at_t,bkeep]; exact v6
  · rw [at_t,bkeep]; exact v28
  · rw [at_t,bkeep,a4]; exact h28
  · rw [at_t,bkeep]; exact v7
  · rw [at_t,bkeep]; exact v12
  · intro k h4 h6 h7 h12 h28 h30
    rw [at_t,bkeep,akeep k h4 h7 h12 h30]; exact hkeep k h6 h28

/-- `x7 - 32` (row 757) as a word address. -/
theorem word_sub (w : Nat) (h : 4≤w) (small : w<2^33) : wordAddress w+signExtend12 4064#12=wordAddress (w-4) := by
  rw [show signExtend12 4064#12=BitVec.ofNat 64 18446744073709551584 by decide]
  unfold wordAddress; rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

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

/-- Rows 749..751 (even quartet). -/
private theorem even_sel (n : MachineState) (g : Nat) (pc : n.pc=address 749) (even : g%2=0)
    (b7 : n.getReg .x7=wordAddress (blockWord g)) (b12 : n.getReg .x12=wordAddress (rebuiltWord g)) :
    let v:=walkRows n evenSel
    legal evenSel n ∧ v.pc=address 771 ∧ v.mem=n.mem ∧ v.getReg .x10=wordAddress (replyWord g) ∧
      v.getReg .x12=wordAddress (rebuiltWord g) ∧ v.getReg .x30=wordAddress (nodeWordOf (g^^^1)) ∧
      (∀ k, k≠.x10 → k≠.x12 → k≠.x30 → v.getReg k=n.getReg k) := by
  obtain ⟨e10,e12,e30⟩ := even_addresses g even
  have r10 : n.getReg .x7+signExtend12 168#12=wordAddress (replyWord g) := by
    rw [b7, show signExtend12 168#12=BitVec.ofNat 64 168 by decide, word_add _ _ (by decide), e10]
  have r30 : n.getReg .x7+signExtend12 136#12=wordAddress (nodeWordOf (g^^^1)) := by
    rw [b7, show signExtend12 136#12=BitVec.ofNat 64 136 by decide, word_add _ _ (by decide), e30]
  refine ⟨legal_of_chain _ _ (by decide) (by simp [evenSel,pcChain,execInstrBr,pc,address]),?_,?_,?_,?_,?_,?_⟩
  all_goals simp [evenSel,walkRows,execInstrBr,pc,address,show signExtend21 80#21=80#64 by decide]
  all_goals first | (intro k a b c; simp [Ne.symm a,Ne.symm b,Ne.symm c]) | exact r10 | exact b12 | exact r30 | rfl

/-- Rows 769..770 (odd quartet). -/
private theorem odd_sel (n : MachineState) (g : Nat) (pc : n.pc=address 769) (odd : g%2=1) (hg : g<4194304)
    (b7 : n.getReg .x7=wordAddress (blockWord g)) (b12 : n.getReg .x12=wordAddress (rebuiltWord g)) :
    let v:=walkRows n oddSel
    legal oddSel n ∧ v.pc=address 771 ∧ v.mem=n.mem ∧ v.getReg .x10=wordAddress (replyWord g) ∧
      v.getReg .x12=wordAddress (rebuiltWord g) ∧ v.getReg .x30=wordAddress (nodeWordOf (g^^^1)) ∧
      (∀ k, k≠.x10 → k≠.x12 → k≠.x30 → v.getReg k=n.getReg k) := by
  obtain ⟨e10,e12,e30⟩ := odd_addresses g odd
  have r10 : n.getReg .x7+signExtend12 3040#12=wordAddress (replyWord g) := by
    rw [b7,e10,show signExtend12 3040#12=BitVec.ofNat 64 18446744073709550560 by decide]
    unfold wordAddress blockWord
    rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]; omega
  have r30 : n.getReg .x7+signExtend12 3240#12=wordAddress (nodeWordOf (g^^^1)) := by
    rw [b7,e30,show signExtend12 3240#12=BitVec.ofNat 64 18446744073709550760 by decide]
    unfold wordAddress blockWord
    rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]; omega
  refine ⟨legal_of_chain _ _ (by decide) (by simp [oddSel,pcChain,execInstrBr,pc,address]),?_,?_,?_,?_,?_,?_⟩
  all_goals simp [oddSel,walkRows,execInstrBr,pc,address]
  all_goals first | (intro k a b c; simp [Ne.symm a,Ne.symm b,Ne.symm c]) | skip
  exacts [r10, b12, r30]

private theorem call_row (v : MachineState) (pc : v.pc=address 771) :
    let c:=walkRows v callRow
    legal callRow v ∧ c.pc=address 772 ∧ c.mem=v.mem ∧ c.getReg .x13=2 ∧ (∀ k, k≠.x13 → c.getReg k=v.getReg k) := by
  refine ⟨legal_of_chain _ _ (by decide) (by simp [callRow,pcChain,execInstrBr,pc,address]),?_,?_,?_,?_⟩
  all_goals simp [callRow,walkRows,execInstrBr,pc,address,show signExtend12 2#12=2#64 by decide]
  all_goals first | (intro k a; simp [Ne.symm a]) | rfl

/-- The parity flag the head branches on. -/
def oddOf (i : Index) : Bool := decide (i.val/4%2=1)

/-- A new quartet before its inverse call: rows 740..751 or 740..748, 769..770, then 771 (`x10` = its reply,
`x12` = its rebuilt block, `x13 = 2`, `x30` = the address of the sibling group's node, `x7` = its block). -/
theorem head_pre (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (fresh : i.val/4≠last) :
    let t:=walkRows s (preRows (oddOf i))
    legal (preRows (oddOf i)) s ∧ t.pc=address 772 ∧ t.mem=s.mem ∧
      t.getReg .x10=wordAddress (replyWord (i.val/4)) ∧ t.getReg .x12=wordAddress (rebuiltWord (i.val/4)) ∧
      t.getReg .x13=2 ∧ t.getReg .x30=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      t.getReg .x6=BitVec.ofNat 64 i.val ∧ t.getReg .x28=BitVec.ofNat 64 (i.val/4) ∧
      t.getReg .x4=BitVec.ofNat 64 (i.val/4) ∧ t.getReg .x7=wordAddress (blockWord (i.val/4)) ∧
      (∀ k, k≠.x4 → k≠.x6 → k≠.x7 → k≠.x10 → k≠.x12 → k≠.x13 → k≠.x28 → k≠.x30 → t.getReg k=s.getReg k) := by
  have hi : i.val<16777216 := i.isLt
  obtain ⟨nl,npc,nmem,n6,n28,n4,n7,n12,nkeep⟩ := new_part s i ord left last r fresh
  set n:=walkRows s newPart with hn
  have sel : ∃ v, v=walkRows n (selRows (oddOf i)) ∧ legal (selRows (oddOf i)) n ∧ v.pc=address 771 ∧
      v.mem=n.mem ∧ v.getReg .x10=wordAddress (replyWord (i.val/4)) ∧
      v.getReg .x12=wordAddress (rebuiltWord (i.val/4)) ∧ v.getReg .x30=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      (∀ k, k≠.x10 → k≠.x12 → k≠.x30 → v.getReg k=n.getReg k) := by
    rcases Nat.mod_two_eq_zero_or_one (i.val/4) with h|h
    · rw [if_neg (by omega)] at npc
      have sr : selRows (oddOf i)=evenSel := by simp [selRows,oddOf,h]
      rw [sr]; exact ⟨_,rfl,even_sel n _ npc h n7 n12⟩
    · rw [if_pos h] at npc
      have sr : selRows (oddOf i)=oddSel := by simp [selRows,oddOf,h]
      rw [sr]; exact ⟨_,rfl,odd_sel n _ npc h (by omega) n7 n12⟩
  obtain ⟨v,hv,sl,vpc,vmem,v10,v12,v30,vkeep⟩ := sel
  obtain ⟨cl,cpc,cmem,c13,ckeep⟩ := call_row v vpc
  have split : preRows (oddOf i)=newPart++selRows (oddOf i)++callRow := rfl
  have mid : walkRows s (newPart++selRows (oddOf i))=v := by rw [walk_join, hv]
  have at_t : walkRows s (preRows (oddOf i))=walkRows v callRow := by rw [split, walk_join, mid]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [split]; refine legal_append _ _ _ (legal_append _ _ _ nl sl) ?_; rw [mid]; exact cl
  · rw [at_t]; exact cpc
  · rw [at_t, cmem, vmem]; exact nmem
  · rw [at_t, ckeep _ (by decide)]; exact v10
  · rw [at_t, ckeep _ (by decide)]; exact v12
  · rw [at_t]; exact c13
  · rw [at_t, ckeep _ (by decide)]; exact v30
  · rw [at_t, ckeep _ (by decide), vkeep _ (by decide) (by decide) (by decide)]; exact n6
  · rw [at_t, ckeep _ (by decide), vkeep _ (by decide) (by decide) (by decide)]; exact n28
  · rw [at_t, ckeep _ (by decide), vkeep _ (by decide) (by decide) (by decide)]; exact n4
  · rw [at_t, ckeep _ (by decide), vkeep _ (by decide) (by decide) (by decide)]; exact n7
  · intro k h4 h6 h7 h10 h12 h13 h28 h30
    rw [at_t, ckeep k h13, vkeep k h10 h12 h30]; exact nkeep k h4 h6 h7 h12 h28 h30

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
theorem ptr_row (u : MachineState) (q : Nat) (hq : q<4194304) (pc : u.pc=address 775)
    (b7 : u.getReg .x7=wordAddress (blockWord q)) :
    let v:=walkRows u ptrRows
    legal ptrRows u ∧ v.pc=address 776 ∧ (∀ k, v.getReg k=u.getReg k) ∧
      (∀ w, w<2^33 → memoryView v w=writeWord (memoryView u) (pointerWord q) (u.getReg .x30) w) := by
  have ad : u.getReg .x7+signExtend12 712#12=wordAddress (pointerWord q) := by rw [b7]; exact pointer_word_eq q
  have room : pointerWord q<2^33 := by unfold pointerWord rebuiltWord blockWord; omega
  have ok : accessValid (wordAddress (pointerWord q)) 8=true :=
    Opening.aligned_access (8*pointerWord q) (by omega) (by unfold MEMORY_BYTES; omega)
  have smem : (walkRows u ptrRows).mem=(u.setMem (wordAddress (pointerWord q)) (u.getReg .x30)).mem := by
    simp [ptrRows,walkRows,execInstrBr,ad]
  refine ⟨⟨pc,?_,trivial⟩,?_,?_,?_⟩
  · simp [ordinaryStep,memoryArgumentsValid,memAccess,ad,ok]
  · simp [ptrRows,walkRows,execInstrBr,pc,address]
  · intro k; simp [ptrRows,walkRows,execInstrBr]
  · intro w hw
    change (walkRows u ptrRows).mem (wordAddress w)=_
    rw [smem]
    exact memory_at_store (state:=u) (address:=pointerWord q) (index:=w) (value:=u.getReg .x30) (by omega) (by omega)

/-- A new quartet after its inverse reply landed in the rebuilt block: rows 773..776 (`x13 := 1`,
`x12 := 1536`, the sibling group's node address to the pointer word, `x10 := 1024`). -/
theorem head_post (a : MachineState) (i : Index) (pc : a.pc=address 773)
    (b7 : a.getReg .x7=wordAddress (blockWord (i.val/4))) :
    let t:=walkRows a headPost
    legal headPost a ∧ t.pc=address 777 ∧ t.getReg .x10=1024 ∧ t.getReg .x12=1536 ∧ t.getReg .x13=1 ∧
      (∀ k, k≠.x10 → k≠.x12 → k≠.x13 → t.getReg k=a.getReg k) ∧
      (∀ w, w<2^33 → memoryView t w=writeWord (memoryView a) (pointerWord (i.val/4)) (a.getReg .x30) w) := by
  have hi : i.val<16777216 := i.isLt
  set u:=walkRows a restoreRows with hu
  have ul : legal restoreRows a ∧ u.pc=address 775 ∧ u.mem=a.mem ∧ u.getReg .x12=1536 ∧
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
