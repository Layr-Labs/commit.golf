import CommitGolfCandidate.K3OpenCopy
import CommitGolfCandidate.K3OpenCall
import CommitGolfCandidate.K1OpenSalt
import CommitGolfCandidate.GroupOpenMemory

/-! K3-lite prefix, one position: addresses, entry registers and the three head paths (rows 740..776). -/
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
/-- reply_E of an even quartet `q` (`[B_q+168, B_q+368)`); also the word of its d3. -/
def replyEWord (q : Nat) := blockWord q+21
/-- Level-22 node of group `h`: G_E at `B_e+336` (even `h`), G_O at `B_e+368` (odd `h`), `e = 2 (h/2)`. -/
def nodeWordOf (h : Nat) := blockWord (2*(h/2))+42+4*(h%2)
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
  input : s.getReg .x10=1024
  output : s.getReg .x12=1536
  selector : s.getReg .x5=0
  width : s.getReg .x11=200
  primitive : s.getReg .x13=1
  index : s.getReg .x14=indexAt ord
  leftReg : s.getReg .x17=countWord left
  salt : s.getReg .x22=9126809632
  base : s.getReg .x26=4096
  divReg : s.getReg .x29=11

/-- Entry of position `i` at ordinal `ord` (`left` to go), `x4` = the previous position's quartet `last`. -/
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

/-- Rows 740..742 when the quartet repeats: nothing but `x6`, `x28`, then on to row 777. -/
theorem head_skip (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (same : i.val/4=last) :
    let t:=walkRows s headRows
    legal headRows s ∧ t.pc=address 777 ∧ t.mem=s.mem ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      (∀ k, k≠.x6 → k≠.x28 → t.getReg k=s.getReg k) := by
  have ld := load_ok s i ord left last r
  have eq := same_quartet i last r.small
  rw [same] at eq; simp only [decide_true] at eq
  have q := quarter i
  rw [same] at q
  refine ⟨?_,?_,?_,?_,?_⟩
  · show legal ((740,.LD .x6 .x14 0)::[(741,.SRLI .x28 .x6 2),(742,.BEQ .x28 .x4 140)]) s
    exact ⟨r.pc,plain_step _ _ rfl ld,legal_of_chain _ _ (by decide) (by simp [pcChain,execInstrBr,r.pc,address])⟩
  all_goals simp [headRows,walkRows,execInstrBr,r.pc,r.index,r.loaded,r.quartet,address,
    q,eq,show signExtend12 0#12=0#64 by decide,show signExtend13 140#13=140#64 by decide]
  all_goals first | (intro k a b; simp [Ne.symm a,Ne.symm b]) | rfl

theorem block_value (i : Index) :
    ((BitVec.ofNat 64 i.val >>> (3:Nat)) <<< (11:Nat))+BitVec.ofNat 64 groupSlots=
      wordAddress (blockWord (2*(i.val/4/2))) := by
  have hi : i.val<16777216 := i.isLt
  rw [shift_right_nat _ _ (by omega), shift_left_nat, ← BitVec.ofNat_add]
  unfold wordAddress blockWord groupSlots trapdoorBase LENGTH LOG_LENGTH
  congr 1; omega

theorem word_add (w c : Nat) (h : c%8=0) : wordAddress w+BitVec.ofNat 64 c=wordAddress (w+c/8) := by
  unfold wordAddress; rw [← BitVec.ofNat_add]; congr 1; omega

/-- Rows 740..748 of a new quartet (`x4 := q`), up to the parity branch at 748. -/
private def newPart : List Row := headRows ++ newRows
private def aluRows : List Row := [(743,.ADDI .x4 .x28 0),(744,.SRLI .x7 .x6 3),(745,.SLLI .x7 .x7 11),
  (746,.ADD .x7 .x7 .x24),(747,.ANDI .x30 .x6 4)]

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
  · show legal ((740,.LD .x6 .x14 0)::[(741,.SRLI .x28 .x6 2),(742,.BEQ .x28 .x4 140)]) s
    exact ⟨r.pc,plain_step _ _ rfl ld,legal_of_chain _ _ (by decide) (by simp [pcChain,execInstrBr,r.pc,address])⟩
  all_goals simp [headRows,walkRows,execInstrBr,r.pc,r.index,r.loaded,r.quartet,address,
    q,eq,ne,show signExtend12 0#12=0#64 by decide]
  all_goals first | (intro k a b; simp [Ne.symm a,Ne.symm b]) | rfl

private theorem alu_part (u : MachineState) (pc : u.pc=address 743) :
    let v:=walkRows u aluRows
    legal aluRows u ∧ v.pc=address 748 ∧ v.mem=u.mem ∧ v.getReg .x4=u.getReg .x28 ∧
      v.getReg .x7=((u.getReg .x6 >>> (3:Nat)) <<< (11:Nat))+u.getReg .x24 ∧
      v.getReg .x30=(u.getReg .x6 &&& signExtend12 4#12) ∧
      (∀ k, k≠.x4 → k≠.x7 → k≠.x30 → v.getReg k=u.getReg k) := by
  refine ⟨legal_of_chain _ _ (by decide) (by simp [aluRows,pcChain,execInstrBr,pc,address]),?_,?_,?_,?_,?_,?_⟩
  · simp [aluRows,walkRows,execInstrBr,pc,address]
  · simp [aluRows,walkRows,execInstrBr]
  · simp [aluRows,walkRows,execInstrBr,show signExtend12 0#12=0#64 by decide]
  · simp [aluRows,walkRows,execInstrBr]
  · simp [aluRows,walkRows,execInstrBr]
  · intro k a b c; simp [aluRows,walkRows,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c]

private theorem new_part (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (fresh : i.val/4≠last) :
    let t:=walkRows s newPart
    legal newPart s ∧ t.pc=(if i.val/4%2=1 then address 764 else address 749) ∧ t.mem=s.mem ∧
      t.getReg .x6=BitVec.ofNat 64 i.val ∧ t.getReg .x28=BitVec.ofNat 64 (i.val/4) ∧
      t.getReg .x4=BitVec.ofNat 64 (i.val/4) ∧ t.getReg .x7=wordAddress (blockWord (2*(i.val/4/2))) ∧
      (∀ k, k≠.x4 → k≠.x6 → k≠.x7 → k≠.x28 → k≠.x30 → t.getReg k=s.getReg k) := by
  obtain ⟨hl,hpc,hmem,h6,h28,hkeep⟩ := new_head s i ord left last r fresh
  set u:=walkRows s headRows with hu
  obtain ⟨al,apc,amem,a4,a7,a30,akeep⟩ := alu_part u hpc
  set v:=walkRows u aluRows with hv
  have v6 : v.getReg .x6=BitVec.ofNat 64 i.val := (akeep _ (by decide) (by decide) (by decide)).trans h6
  have v28 : v.getReg .x28=BitVec.ofNat 64 (i.val/4) := (akeep _ (by decide) (by decide) (by decide)).trans h28
  have v7 : v.getReg .x7=wordAddress (blockWord (2*(i.val/4/2))) := by
    rw [a7,h6,hkeep _ (by decide) (by decide),r.slots]; exact block_value i
  have v30 : v.getReg .x30=BitVec.ofNat 64 (4*(i.val/4%2)) := by rw [a30,h6]; exact and_four i.val
  let br : List Row := [(748,.BNE .x30 .x0 64)]
  have taken (nz : v.getReg .x30≠0#64) : execInstrBr v (.BNE .x30 .x0 64)=v.setPC (address 764) := by
    have yes : (v.getReg .x30 != v.getReg .x0)=true := by simp [open_zero,nz]
    simp only [execInstrBr,yes,ite_true,apc]
    exact congrArg v.setPC (by decide : address 748+signExtend13 64=address 764)
  have fall (z : v.getReg .x30=0#64) : execInstrBr v (.BNE .x30 .x0 64)=v.setPC (address 749) := by
    simp only [execInstrBr,open_zero,z,beq_self_eq_true,ite_true,apc]
    exact congrArg v.setPC (by decide : address 748+4=address 749)
  have bl : legal br v ∧ (walkRows v br).pc=(if i.val/4%2=1 then address 764 else address 749) ∧
      (walkRows v br).mem=v.mem ∧ (∀ k, (walkRows v br).getReg k=v.getReg k) := by
    refine ⟨⟨apc,plain_step _ _ rfl (no_mem_valid _ _ rfl),trivial⟩,?_,?_,?_⟩
    · show (execInstrBr v (.BNE .x30 .x0 64)).pc=_
      rcases Nat.mod_two_eq_zero_or_one (i.val/4) with h|h
      · rw [fall (by rw [v30,h]), if_neg (by omega)]; rfl
      · rw [taken (by rw [v30,h]; decide), if_pos h]; rfl
    · exact bne_mem' v _ _ _
    · intro k; exact bne_reg' v _ _ _ _
  have split : newPart=headRows++aluRows++br := rfl
  have at_t : walkRows s newPart=walkRows v br := by rw [split,walk_join,walk_join]
  obtain ⟨bl1,bpc,bmem,bkeep⟩ := bl
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [split]; exact legal_append _ _ _ (legal_append _ _ _ hl al) bl1
  · rw [at_t]; exact bpc
  · rw [at_t,bmem,amem,hmem]
  · rw [at_t,bkeep]; exact v6
  · rw [at_t,bkeep]; exact v28
  · rw [at_t,bkeep,a4]; exact h28
  · rw [at_t,bkeep]; exact v7
  · intro k h4 h6 h7 h28 h30
    rw [at_t,bkeep,akeep k h4 h7 h30]; exact hkeep k h6 h28

theorem sib_args (q : Nat) (hq : q<4194304) :
    PairArgs (nodeWordOf (q^^^1)) (heapWord (4194304+(q^^^1))) sibPairs := by
  have gx := xor_one_lt q 22 hq (by decide)
  obtain ⟨d,m⟩ := xor_one q
  refine ⟨by decide,?_,?_⟩
  · intro p hp
    simp only [sibPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    unfold nodeWordOf blockWord heapWord
    rcases hp with rfl|rfl|rfl|rfl <;> constructor <;> omega
  · intro p hp p' hp'
    simp only [sibPairs,List.mem_cons,List.not_mem_nil,or_false] at hp hp'
    unfold nodeWordOf blockWord heapWord
    rcases hp with rfl|rfl|rfl|rfl <;> rcases hp' with rfl|rfl|rfl|rfl <;> omega

/-- Rows 765..776: heap slot of the level-22 sibling and its 32-byte copy from `x30`. -/
theorem sib_rows (u : MachineState) (i : Index) (pc : u.pc=address 765) (q28 : u.getReg .x28=BitVec.ofNat 64 (i.val/4))
    (lv : u.getReg .x19=4194304) (hp : u.getReg .x9=BitVec.ofNat 64 trapdoorBase)
    (src : u.getReg .x30=wordAddress (nodeWordOf (i.val/4^^^1))) :
    let v:=walkRows u sibRows
    legal sibRows u ∧ v.pc=address 777 ∧
      (∀ k, k≠.x28 → k≠.x31 → v.getReg k=u.getReg k) ∧
      (∀ w, w<2^33 → memoryView v w=pairView (memoryView u) (memoryView u) (nodeWordOf (i.val/4^^^1))
        (heapWord (4194304+(i.val/4^^^1))) sibPairs w) := by
  have hi : i.val<16777216 := i.isLt
  have gx := xor_one_lt (i.val/4) 22 (by omega) (by decide)
  have x := xor_low (i.val/4)
  have value : ((BitVec.ofNat 64 (i.val/4^^^1)+4194304) <<< (5:Nat))+BitVec.ofNat 64 trapdoorBase=
      wordAddress (heapWord (4194304+(i.val/4^^^1))) := by
    rw [show (4194304 : Word)=BitVec.ofNat 64 4194304 from rfl, ← BitVec.ofNat_add, shift_left_nat, ← BitVec.ofNat_add]
    unfold wordAddress heapWord trapdoorBase LENGTH LOG_LENGTH; congr 1; omega
  set a:=walkRows u [(765,.XORI .x28 .x28 1),(766,.ADD .x28 .x28 .x19),(767,.SLLI .x28 .x28 5),(768,.ADD .x28 .x28 .x9)]
    with ha
  have al : legal [(765,.XORI .x28 .x28 1),(766,.ADD .x28 .x28 .x19),(767,.SLLI .x28 .x28 5),(768,.ADD .x28 .x28 .x9)] u ∧
      a.pc=address 769 ∧ a.mem=u.mem ∧
      a.getReg .x28=(((u.getReg .x28 ^^^ signExtend12 1#12)+u.getReg .x19) <<< (5:Nat))+u.getReg .x9 ∧
      (∀ k, k≠.x28 → a.getReg k=u.getReg k) := by
    refine ⟨legal_of_chain _ _ (by decide) (by simp [pcChain,execInstrBr,pc,address]),?_,?_,?_,?_⟩
    · simp [ha,walkRows,execInstrBr,pc,address]
    · simp [ha,walkRows,execInstrBr]
    · simp [ha,walkRows,execInstrBr]
    · intro k h; simp [ha,walkRows,execInstrBr,Ne.symm h]
  obtain ⟨l1,apc,amem,a28',akeep⟩ := al
  have a28 : a.getReg .x28=wordAddress (heapWord (4194304+(i.val/4^^^1))) := by
    rw [a28',q28,lv,hp,x]; exact value
  obtain ⟨pl,ppc,pkeep,pview⟩ := pair_rows_run sibPairs a 769 .x30 .x28 _ _ (by decide) (by decide) apc
    ((akeep .x30 (by decide)).trans src) a28 (sib_args _ (by omega))
  have split : sibRows=[(765,.XORI .x28 .x28 1),(766,.ADD .x28 .x28 .x19),(767,.SLLI .x28 .x28 5),(768,.ADD .x28 .x28 .x9)]
    ++pairRows 769 .x30 .x28 sibPairs := rfl
  refine ⟨?_,?_,?_,?_⟩
  · rw [split]; exact legal_append _ _ _ l1 pl
  · rw [split, walk_join]; have h := ppc; simp only [sibPairs,List.length_cons,List.length_nil] at h; exact h
  · intro k h28 h31; rw [split, walk_join, pkeep k h31]; exact akeep k h28
  · intro w hw
    rw [split, walk_join, pview w hw]
    refine pair_view_congr sibPairs _ _ _ _ _ _ (sib_args _ (by omega)).room ?_ ?_ w hw
    · intro w' _; change a.mem _=u.mem _; rw [amem]
    · intro q _; change a.mem _=u.mem _; rw [amem]

/-- New odd quartet: rows 740..748, 764, 765..776 (sibling G_E). -/
theorem head_odd (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (fresh : i.val/4≠last) (odd : i.val/4%2=1) :
    let t:=walkRows s oddPath
    legal oddPath s ∧ t.pc=address 777 ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧ t.getReg .x4=BitVec.ofNat 64 (i.val/4) ∧
      (∀ k, k≠.x4 → k≠.x6 → k≠.x7 → k≠.x28 → k≠.x30 → k≠.x31 → t.getReg k=s.getReg k) ∧
      (∀ w, w<2^33 → memoryView t w=pairView (memoryView s) (memoryView s) (nodeWordOf (i.val/4^^^1))
        (heapWord (4194304+(i.val/4^^^1))) sibPairs w) := by
  obtain ⟨nl,npc,nmem,n6,n28,n4,n7,nkeep⟩ := new_part s i ord left last r fresh
  rw [if_pos odd] at npc
  set n:=walkRows s newPart with hn
  set u:=walkRows n oddRow with hu
  have src : u.getReg .x30=wordAddress (nodeWordOf (i.val/4^^^1)) := by
    obtain ⟨d,m⟩ := xor_one (i.val/4)
    have e : nodeWordOf (i.val/4^^^1)=blockWord (2*(i.val/4/2))+42 := by
      unfold nodeWordOf; rw [d,m,odd]
    rw [e, ← word_add _ 336 (by decide)]
    simp [hu,oddRow,walkRows,execInstrBr,n7,show signExtend12 336#12=336#64 by decide]
  have ul : legal oddRow n ∧ u.pc=address 765 ∧ u.mem=n.mem ∧ (∀ k, k≠.x30 → u.getReg k=n.getReg k) := by
    refine ⟨legal_of_chain _ _ (by decide) (by simp [oddRow,pcChain,execInstrBr,npc,address]),?_,?_,?_⟩
    all_goals simp [hu,oddRow,walkRows,execInstrBr,npc,address]
    all_goals first | (intro k h; simp [Ne.symm h]) | rfl
  obtain ⟨ol,upc,umem,ukeep⟩ := ul
  obtain ⟨sl,spc,skeep,sview⟩ := sib_rows u i upc ((ukeep _ (by decide)).trans n28)
    ((ukeep _ (by decide)).trans ((nkeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans r.leaves))
    ((ukeep _ (by decide)).trans ((nkeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans r.heap)) src
  have split : oddPath=newPart++oddRow++sibRows := rfl
  have at_t : walkRows s oddPath=walkRows u sibRows := by rw [split, walk_join, walk_join]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [split]; exact legal_append _ _ _ (legal_append _ _ _ nl ol) sl
  · rw [at_t]; exact spc
  · rw [at_t, skeep _ (by decide) (by decide), ukeep _ (by decide)]; exact n6
  · rw [at_t, skeep _ (by decide) (by decide), ukeep _ (by decide)]; exact n4
  · intro k h4 h6 h7 h28 h30 h31
    rw [at_t, skeep _ h28 h31, ukeep _ h30]; exact nkeep k h4 h6 h7 h28 h30
  · intro w hw
    rw [at_t, sview w hw]
    refine pair_view_congr sibPairs _ _ _ _ _ _ (sib_args _ (by have : i.val<16777216 := i.isLt; omega)).room ?_ ?_ w hw
    · intro w' _; change u.mem _=s.mem _; rw [umem.trans nmem]
    · intro q _; change u.mem _=s.mem _; rw [umem.trans nmem]

/-- New even quartet before its inverse call: rows 740..750 (`x10` = reply_E, `x13 = 2`). -/
theorem head_even_pre (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (fresh : i.val/4≠last) (even : i.val/4%2=0) :
    let t:=walkRows s evenPre
    legal evenPre s ∧ t.pc=address 751 ∧ t.mem=s.mem ∧
      t.getReg .x10=wordAddress (replyEWord (i.val/4)) ∧ t.getReg .x13=2 ∧
      t.getReg .x6=BitVec.ofNat 64 i.val ∧ t.getReg .x28=BitVec.ofNat 64 (i.val/4) ∧
      t.getReg .x4=BitVec.ofNat 64 (i.val/4) ∧ t.getReg .x7=wordAddress (blockWord (i.val/4)) ∧
      (∀ k, k≠.x4 → k≠.x6 → k≠.x7 → k≠.x10 → k≠.x13 → k≠.x28 → k≠.x30 → t.getReg k=s.getReg k) := by
  obtain ⟨nl,npc,nmem,n6,n28,n4,n7,nkeep⟩ := new_part s i ord left last r fresh
  rw [if_neg (by omega)] at npc
  have e : 2*(i.val/4/2)=i.val/4 := by omega
  rw [e] at n7
  set n:=walkRows s newPart with hn
  have reply : n.getReg .x7+signExtend12 168#12=wordAddress (replyEWord (i.val/4)) := by
    rw [n7, show signExtend12 168#12=BitVec.ofNat 64 168 by decide, word_add _ _ (by decide)]; rfl
  have il : legal invRows n ∧ (walkRows n invRows).pc=address 751 ∧ (walkRows n invRows).mem=n.mem ∧
      (walkRows n invRows).getReg .x10=wordAddress (replyEWord (i.val/4)) ∧ (walkRows n invRows).getReg .x13=2 ∧
      (∀ k, k≠.x10 → k≠.x13 → (walkRows n invRows).getReg k=n.getReg k) := by
    refine ⟨legal_of_chain _ _ (by decide) (by simp [invRows,pcChain,execInstrBr,npc,address]),?_,?_,?_,?_,?_⟩
    all_goals simp [invRows,walkRows,execInstrBr,npc,address,show signExtend12 2#12=2#64 by decide]
    all_goals first | (intro k a b; simp [Ne.symm a,Ne.symm b]) | exact reply | rfl
  obtain ⟨l2,ipc,imem,i10,i13,ikeep⟩ := il
  have split : evenPre=newPart++invRows := rfl
  have at_t : walkRows s evenPre=walkRows n invRows := by rw [split, walk_join]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [split]; exact legal_append _ _ _ nl l2
  · rw [at_t]; exact ipc
  · rw [at_t, imem]; exact nmem
  · rw [at_t]; exact i10
  · rw [at_t]; exact i13
  · rw [at_t, ikeep _ (by decide) (by decide)]; exact n6
  · rw [at_t, ikeep _ (by decide) (by decide)]; exact n28
  · rw [at_t, ikeep _ (by decide) (by decide)]; exact n4
  · rw [at_t, ikeep _ (by decide) (by decide)]; exact n7
  · intro k h4 h6 h7 h10 h13 h28 h30
    rw [at_t, ikeep _ h10 h13]; exact nkeep k h4 h6 h7 h28 h30

theorem d3_args (q : Nat) (hq : q<4194304) : PairArgs 192 (blockWord q) d3Pairs := by
  refine ⟨by decide,?_,?_⟩
  · intro p hp
    simp only [d3Pairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    unfold blockWord
    rcases hp with rfl|rfl|rfl|rfl <;> constructor <;> omega
  · intro p hp p' hp'
    simp only [d3Pairs,List.mem_cons,List.not_mem_nil,or_false] at hp hp'
    unfold blockWord
    rcases hp with rfl|rfl|rfl|rfl <;> rcases hp' with rfl|rfl|rfl|rfl <;> omega

/-- New even quartet after the inverse reply landed in `[1536, 1736)`: rows 752..763 (d3 back to `B_q+168`,
`x10 := 1024`, `x13 := 1`, sibling G_O) and 765..776. -/
theorem head_even_post (a : MachineState) (i : Index) (pc : a.pc=address 752) (even : i.val/4%2=0)
    (out : a.getReg .x12=wordAddress 192) (q28 : a.getReg .x28=BitVec.ofNat 64 (i.val/4))
    (b7 : a.getReg .x7=wordAddress (blockWord (i.val/4)))
    (lv : a.getReg .x19=4194304) (hp : a.getReg .x9=BitVec.ofNat 64 trapdoorBase) :
    let t:=walkRows a evenPost
    legal evenPost a ∧ t.pc=address 777 ∧ t.getReg .x10=1024 ∧ t.getReg .x13=1 ∧
      (∀ k, k≠.x10 → k≠.x13 → k≠.x28 → k≠.x30 → k≠.x31 → t.getReg k=a.getReg k) ∧
      (∀ w, w<2^33 → memoryView t w=pairView (pairView (memoryView a) (memoryView a) 192 (blockWord (i.val/4)) d3Pairs)
        (memoryView a) (nodeWordOf (i.val/4^^^1)) (heapWord (4194304+(i.val/4^^^1))) sibPairs w) := by
  have hi : i.val<16777216 := i.isLt
  obtain ⟨dl,dpc,dkeep,dview⟩ := pair_rows_run d3Pairs a 752 .x12 .x7 192 (blockWord (i.val/4)) (by decide) (by decide)
    pc out b7 (d3_args _ (by omega))
  set d:=walkRows a (pairRows 752 .x12 .x7 d3Pairs) with hd
  have dp : d.pc=address 760 := by have h := dpc; simp only [d3Pairs,List.length_cons,List.length_nil] at h; exact h
  set tail : List Row := [(760,.ADDI .x10 .x0 1024),(761,.ADDI .x13 .x0 1),(762,.ADDI .x30 .x7 368),(763,.JAL .x0 8)]
    with htail
  have node : d.getReg .x7+signExtend12 368#12=wordAddress (nodeWordOf (i.val/4^^^1)) := by
    obtain ⟨dd,m⟩ := xor_one (i.val/4)
    have e : nodeWordOf (i.val/4^^^1)=blockWord (i.val/4)+46 := by
      unfold nodeWordOf; rw [dd,m,even]; unfold blockWord; omega
    rw [dkeep _ (by decide), b7, e, show signExtend12 368#12=BitVec.ofNat 64 368 by decide, word_add _ _ (by decide)]
  have tl : legal tail d ∧ (walkRows d tail).pc=address 765 ∧ (walkRows d tail).mem=d.mem ∧
      (walkRows d tail).getReg .x10=1024 ∧ (walkRows d tail).getReg .x13=1 ∧
      (walkRows d tail).getReg .x30=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      (∀ k, k≠.x10 → k≠.x13 → k≠.x30 → (walkRows d tail).getReg k=d.getReg k) := by
    refine ⟨legal_of_chain _ _ (by rw [htail]; decide) (by simp [htail,pcChain,execInstrBr,dp,address,show signExtend21 8#21=8#64 by decide]),
      ?_,?_,?_,?_,?_,?_⟩
    all_goals simp [htail,walkRows,execInstrBr,dp,address,
      show signExtend12 1024#12=1024#64 by decide,show signExtend12 1#12=1#64 by decide,
      show signExtend21 8#21=8#64 by decide]
    all_goals first | (intro k a b c; simp [Ne.symm a,Ne.symm b,Ne.symm c]) | exact node | rfl
  obtain ⟨tl1,tpc,tmem,t10,t13,t30,tkeep⟩ := tl
  set u:=walkRows d tail with hu
  obtain ⟨sl,spc,skeep,sview⟩ := sib_rows u i tpc
    ((tkeep _ (by decide) (by decide) (by decide)).trans ((dkeep _ (by decide)).trans q28))
    ((tkeep _ (by decide) (by decide) (by decide)).trans ((dkeep _ (by decide)).trans lv))
    ((tkeep _ (by decide) (by decide) (by decide)).trans ((dkeep _ (by decide)).trans hp)) t30
  have split : evenPost=pairRows 752 .x12 .x7 d3Pairs++tail++sibRows := rfl
  have at_t : walkRows a evenPost=walkRows u sibRows := by rw [split, walk_join, walk_join]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [split]; exact legal_append _ _ _ (legal_append _ _ _ dl tl1) sl
  · rw [at_t]; exact spc
  · rw [at_t, skeep _ (by decide) (by decide)]; exact t10
  · rw [at_t, skeep _ (by decide) (by decide)]; exact t13
  · intro k h10 h13 h28 h30 h31
    rw [at_t, skeep _ h28 h31, tkeep _ h10 h13 h30, dkeep _ h31]
  · intro w hw
    rw [at_t, sview w hw]
    refine pair_view_congr sibPairs _ _ _ _ _ _ (sib_args _ (by omega)).room ?_ ?_ w hw
    · intro w' hw'; change u.mem _=_; rw [tmem]; exact dview w' hw'
    · intro p hp
      have r : p.1<4 := by revert p; unfold sibPairs; decide
      have room := ((sib_args (i.val/4) (by omega)).room p hp).1
      change u.mem _=_; rw [tmem]
      change memoryView d _=_
      rw [dview _ room]
      apply pair_view_outside
      intro p' hp'
      have r' : 21≤p'.2 ∧ p'.2<25 := by revert p'; unfold d3Pairs; decide
      obtain ⟨dd,m⟩ := xor_one (i.val/4)
      unfold nodeWordOf blockWord; rw [dd,m]; omega

end TwoPermutationPrototype.GroupedOpening
