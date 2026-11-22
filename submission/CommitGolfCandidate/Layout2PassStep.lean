import CommitGolfCandidate.Layout2PassRows
import CommitGolfCandidate.GroupOpenVirtual
import CommitGolfCandidate.Machine
import CommitGolfCandidate.K3OpenReply
import CommitGolfCandidate.Layout2Phase

/-! Layout 2 V2a opener, first pass, one position `i` at ordinal `j` (phase `ph = j % 4`): the head (13 rows), the
inverse call that writes the quartet reply to the record block `B = passDest j`, the pointer to `B+16`, the chained
salt generator (`K3OpenChain`, phase `ph`), the salt to `B+0..15` and the latch. Execution (`per_run`), the state
after a position (`trace_post`) and the fixed-oracle outcome (`fixed_*`). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening
open CommitGolfCandidate.Permutation.CounterSalt (coord)
open TwoPermutationPrototype.Sampling (saltWords)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

theorem view_of_mem {a b : MachineState} (h : a.mem=b.mem) (w : Nat) : memoryView a w=memoryView b w := by
  unfold memoryView MachineState.getMem; rw [h]

/-! ### Geometry of the record blocks -/

/-- Start of record `j`'s block (`Layout2.destOf j`). -/
def passDest (j : Nat) : Nat := proofBase+2136*(j/4)+CommitGolfCandidate.Layout2Phase.phaseBase (j%4)
/-- Its word index. -/
def passWord (j : Nat) : Nat := passDest j/8

theorem pass_dest_aligned (j : Nat) : passDest j%8=0 := by
  have hp : proofBase%8=0 := by decide
  unfold passDest CommitGolfCandidate.Layout2Phase.phaseBase; split_ifs <;> omega

theorem pass_word_mul (j : Nat) : 8*passWord j=passDest j := by
  have := pass_dest_aligned j; unfold passWord; omega

theorem pass_word_address (j : Nat) : wordAddress (passWord j)=BitVec.ofNat 64 (passDest j) := by
  unfold wordAddress; rw [pass_word_mul]

theorem pass_dest_next (j : Nat) : passDest j+passStride (j%4)=passDest (j+1) := by
  unfold passDest CommitGolfCandidate.Layout2Phase.phaseBase passStride
  have h := Nat.mod_lt j (show 4>0 by decide)
  have : (j+1)/4=j/4+(if j%4=3 then 1 else 0) := by split <;> omega
  have : (j+1)%4=(j%4+1)%4 := by omega
  split_ifs at * <;> omega

theorem pass_dest_bound (j : Nat) : proofBase ≤ passDest j ∧ passDest j+passStride (j%4) ≤ proofBase+534*(j+1) := by
  unfold passDest CommitGolfCandidate.Layout2Phase.phaseBase passStride
  have h := Nat.mod_lt j (show 4>0 by decide)
  split_ifs <;> omega

theorem pass_word_room (j : Nat) (hj : j ≤ 16777216) : proofBase/8 ≤ passWord j ∧ passWord j+67 ≤ 2^32 := by
  have b := pass_dest_bound j
  have m := pass_word_mul j
  have pb : proofBase=13824430176 := rfl
  unfold passStride at b
  constructor <;> (split_ifs at b <;> omega)

/-! ### Entry of a position -/

/-- Entry of position `i` at ordinal `ord` (`left` to go): pc at its phase's first word, the block cursor `x29`. -/
structure Entry (s : MachineState) (i : Index) (ord left : Nat) extends Registers s ord left where
  pc : s.pc=address (3079+80*(ord%4))
  one : s.getReg .x23=1
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  leaves : s.getReg .x19=4194304
  slots : s.getReg .x24=BitVec.ofNat 64 groupSlots
  cursor : s.getReg .x29=BitVec.ofNat 64 (passDest ord)
  loaded : s.getMem (indexAt ord)=BitVec.ofNat 64 i.val
  access : accessValid (indexAt ord) 8=true
  sp : s.getReg .x2=BitVec.ofNat 64 tableBase
  mask : s.getReg .x1=65535
  table : TableAt s

private theorem load_ok (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) :
    memoryArgumentsValid s (.LD .x6 .x14 0)=true := by
  simpa [memoryArgumentsValid,memAccess,r.index,show signExtend12 0#12=0#64 by decide] using r.access

/-! ### Head: rows `3079+80ph .. 3091+80ph` -/

private def headA (ph : Nat) : List Row := [(3079+80*ph,.LD .x6 .x14 0),(3080+80*ph,.SRLI .x28 .x6 2),
  (3081+80*ph,.SLLI .x3 .x6 4),(3082+80*ph,.AND .x30 .x3 .x1),(3083+80*ph,.ADD .x30 .x30 .x2)]
private def headB (ph : Nat) : List Row := [(3084+80*ph,.SLLI .x7 .x28 10),(3085+80*ph,.ADD .x7 .x7 .x24),
  (3086+80*ph,.ADDI .x12 .x29 0)]
private def headC (ph : Nat) : List Row := [(3087+80*ph,.LH .x10 .x30 4),(3088+80*ph,.ADD .x10 .x10 .x7),
  (3089+80*ph,.LH .x31 .x30 6),(3090+80*ph,.ADD .x31 .x31 .x7),(3091+80*ph,.ADDI .x13 .x0 2)]
private theorem head_split (ph : Nat) : headRows ph=headA ph++headB ph++headC ph := rfl

private theorem head_a (s : MachineState) (i : Index) (ord left ph : Nat) (hph : ord%4=ph) (hp : ph<4)
    (r : Entry s i ord left) :
    let t:=walkRows s (headA ph)
    legal (headA ph) s ∧ t.pc=address (3084+80*ph) ∧ t.mem=s.mem ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      t.getReg .x28=BitVec.ofNat 64 (i.val/4) ∧ t.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) ∧
      t.getReg .x30=wordAddress (tableWord (i.val%4096)) ∧
      (∀ k, k≠.x6 → k≠.x28 → k≠.x3 → k≠.x30 → t.getReg k=s.getReg k) := by
  have ld := load_ok s i ord left r
  have q := quarter i
  have pc := r.pc
  rw [hph] at pc
  have x6 : (walkRows s (headA ph)).getReg .x6=BitVec.ofNat 64 i.val := by
    simp [headA,walkRows,execInstrBr,r.index,r.loaded,show signExtend12 0#12=0#64 by decide]
  have x28 : (walkRows s (headA ph)).getReg .x28=BitVec.ofNat 64 (i.val/4) := by
    simp [headA,walkRows,execInstrBr,r.index,r.loaded,show signExtend12 0#12=0#64 by decide,q]
  have x3 : (walkRows s (headA ph)).getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) := by
    simp [headA,walkRows,execInstrBr,r.index,r.loaded,show signExtend12 0#12=0#64 by decide]
  have x30 : (walkRows s (headA ph)).getReg .x30=wordAddress (tableWord (i.val%4096)) := by
    simp only [headA,walkRows,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
      Opening.getReg_setReg,r.mask,r.sp]
    simp [r.index,r.loaded,show signExtend12 0#12=0#64 by decide]
    rw [tile16' i, entry_address']
  have mem : (walkRows s (headA ph)).mem=s.mem := by simp [headA,walkRows,execInstrBr]
  have keep : ∀ k, k≠.x6 → k≠.x28 → k≠.x3 → k≠.x30 → (walkRows s (headA ph)).getReg k=s.getReg k := by
    intro k a b c d; simp [headA,walkRows,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d]
  refine ⟨?_,?_,mem,x6,x28,x3,x30,keep⟩
  · interval_cases ph
    all_goals
      show legal (_::_) s
      exact ⟨pc,plain_step _ _ rfl ld,legal_of_chain _ _ (by decide) (by simp [pcChain,execInstrBr,pc,address])⟩
  · interval_cases ph <;> simp [headA,walkRows,execInstrBr,pc,address]

private theorem head_b (a : MachineState) (i : Index) (ph : Nat) (hp : ph<4) (pc : a.pc=address (3084+80*ph))
    (x28 : a.getReg .x28=BitVec.ofNat 64 (i.val/4)) (slots : a.getReg .x24=BitVec.ofNat 64 groupSlots) :
    let b:=walkRows a (headB ph)
    legal (headB ph) a ∧ b.pc=address (3087+80*ph) ∧ b.mem=a.mem ∧
      b.getReg .x7=wordAddress (blockWord (i.val/4)) ∧ b.getReg .x12=a.getReg .x29 ∧
      (∀ k, k≠.x7 → k≠.x12 → b.getReg k=a.getReg k) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · interval_cases ph <;> exact legal_of_chain _ _ (by decide) (by simp [headB,pcChain,execInstrBr,pc,address])
  · interval_cases ph <;> simp [headB,walkRows,execInstrBr,pc,address]
  · simp [headB,walkRows,execInstrBr]
  · simp [headB,walkRows,execInstrBr]
    rw [x28, slots]; exact block_value i
  · simp [headB,walkRows,execInstrBr,show signExtend12 0#12=0#64 by decide]
  · intro k h7 h12; simp [headB,walkRows,execInstrBr,Ne.symm h7,Ne.symm h12]

private theorem head_c (c : MachineState) (i : Index) (ph : Nat) (hp : ph<4) (pc : c.pc=address (3087+80*ph))
    (x30 : c.getReg .x30=wordAddress (tableWord (i.val%4096))) (x7 : c.getReg .x7=wordAddress (blockWord (i.val/4)))
    (tab : TableAt c) :
    let d:=walkRows c (headC ph)
    legal (headC ph) c ∧ d.pc=address (3092+80*ph) ∧ d.mem=c.mem ∧
      d.getReg .x10=wordAddress (replyWord (i.val/4)) ∧ d.getReg .x31=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      d.getReg .x13=2 ∧ (∀ k, k≠.x10 → k≠.x31 → k≠.x13 → d.getReg k=c.getReg k) := by
  have hi : i.val<16777216 := i.isLt
  have he : i.val%4096<4096 := Nat.mod_lt _ (by decide)
  obtain ⟨hR,hG⟩ := entry_half c _ he tab
  have fit : 8*tableWord (i.val%4096)+8 ≤ 2^36 := by simp only [tableWord]; omega
  have v4 : accessValid (wordAddress (tableWord (i.val%4096))+signExtend12 4#12) 2=true := by
    rw [show signExtend12 4#12=BitVec.ofNat 64 4 by decide]; unfold wordAddress; rw [← BitVec.ofNat_add]
    exact table_access _ 2 (by omega) (by omega)
  have v6 : accessValid (wordAddress (tableWord (i.val%4096))+signExtend12 6#12) 2=true := by
    rw [show signExtend12 6#12=BitVec.ofNat 64 6 by decide]; unfold wordAddress; rw [← BitVec.ofNat_add]
    exact table_access _ 2 (by omega) (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · interval_cases ph <;>
      simp [headC,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,x30,v4,v6,address]
  · interval_cases ph <;> simp [headC,walkRows,execInstrBr,pc,address]
  · simp [headC,walkRows,execInstrBr]
  · have e1 : (walkRows c (headC ph)).getReg .x10=
        (c.getHalfword (c.getReg .x30+signExtend12 4#12)).signExtend 64+c.getReg .x7 := rfl
    rw [e1, x30, hR, x7]; exact reply_offset i
  · have e1 : (walkRows c (headC ph)).getReg .x31=
        (c.getHalfword (c.getReg .x30+signExtend12 6#12)).signExtend 64+c.getReg .x7 := rfl
    rw [e1, x30, hG, x7]; exact node_offset i
  · simp [headC,walkRows,execInstrBr,show signExtend12 2#12=2#64 by decide]
  · intro k h10 h31 h13; simp [headC,walkRows,execInstrBr,Ne.symm h10,Ne.symm h31,Ne.symm h13]

/-- The head rows: the reply address in `x10`, the block in `x12`, the sibling node's address in `x31`. -/
theorem head_run (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) :
    let ph:=ord%4
    let t:=walkRows s (headRows ph)
    legal (headRows ph) s ∧ t.pc=address (3092+80*ph) ∧ t.mem=s.mem ∧
      t.getReg .x10=wordAddress (replyWord (i.val/4)) ∧ t.getReg .x12=wordAddress (passWord ord) ∧
      t.getReg .x13=2 ∧ t.getReg .x31=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      t.getReg .x6=BitVec.ofNat 64 i.val ∧ t.getReg .x28=BitVec.ofNat 64 (i.val/4) ∧
      t.getReg .x7=wordAddress (blockWord (i.val/4)) ∧
      t.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) ∧ t.getReg .x30=wordAddress (tableWord (i.val%4096)) ∧
      (∀ k, k≠.x6 → k≠.x7 → k≠.x10 → k≠.x12 → k≠.x13 → k≠.x28 → k≠.x30 → k≠.x31 → k≠.x3 →
        t.getReg k=s.getReg k) := by
  intro ph t
  have hp : ph<4 := Nat.mod_lt _ (by decide)
  obtain ⟨la,apc,amem,a6,a28,a3,a30,akeep⟩ := head_a s i ord left ph rfl hp r
  set a:=walkRows s (headA ph) with ha
  obtain ⟨lb,bpc,bmem,b7,b12,bkeep⟩ := head_b a i ph hp apc a28
    ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans r.slots)
  set b:=walkRows a (headB ph) with hb
  have btab : TableAt b := by
    intro e' he' h' hh'
    rw [view_of_mem (bmem.trans amem)]; exact r.table e' he' h' hh'
  obtain ⟨lc,cpc,cmem,c10,c31,c13,ckeep⟩ := head_c b i ph hp bpc
    ((bkeep _ (by decide) (by decide)).trans a30) b7 btab
  have at_t : t=walkRows b (headC ph) := by
    show walkRows s (headRows ph)=_; rw [head_split, walk_join, walk_join]
  have kb (k : Reg) (h7 : k≠.x7) (h12 : k≠.x12) (h10 : k≠.x10) (h31 : k≠.x31) (h13 : k≠.x13) :
      t.getReg k=a.getReg k := by rw [at_t, ckeep k h10 h31 h13, bkeep k h7 h12]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [head_split]; exact legal_append _ _ _ (legal_append _ _ _ la lb) (by rw [walk_join]; exact lc)
  · rw [at_t]; exact cpc
  · rw [at_t, cmem, bmem]; exact amem
  · rw [at_t]; exact c10
  · rw [at_t, ckeep _ (by decide) (by decide) (by decide), b12,
      akeep _ (by decide) (by decide) (by decide) (by decide), r.cursor, pass_word_address]
  · rw [at_t]; exact c13
  · rw [at_t]; exact c31
  · rw [kb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a6
  · rw [kb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a28
  · rw [at_t, ckeep _ (by decide) (by decide) (by decide)]; exact b7
  · rw [kb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a3
  · rw [kb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a30
  · intro k h6 h7 h10 h12 h13 h28 h30 h31 h3
    rw [kb k h7 h12 h10 h31 h13]; exact akeep k h6 h28 h3 h30

/-! ### After the inverse call: rows `3093+80ph .. 3096+80ph` -/

/-- The state after the inverse call wrote `y` to the block. -/
def called (s : MachineState) (ord : Nat) (y : BitVec 1600) : MachineState :=
  writeBits (walkRows s (headRows (ord%4))) (wordAddress (passWord ord)) y

/-- The head of a position: rows, the inverse reply `y` at the block, the pointer and the generator input. -/
def headed (s : MachineState) (ord : Nat) (y : BitVec 1600) : MachineState :=
  walkRows (called s ord y) (postRows (ord%4))

theorem post_run (a : MachineState) (ord : Nat) (ph : Nat) (hp : ph<4) (pc : a.pc=address (3093+80*ph))
    (cur : a.getReg .x29=BitVec.ofNat 64 (passDest ord)) (hj : ord ≤ 16777216) :
    let t:=walkRows a (postRows ph)
    legal (postRows ph) a ∧ t.pc=address (3097+80*ph) ∧ t.getReg .x10=1024 ∧ t.getReg .x12=1536 ∧
      t.getReg .x13=1 ∧ (∀ k, k≠.x10 → k≠.x12 → k≠.x13 → t.getReg k=a.getReg k) ∧
      (∀ w, w<2^33 → memoryView t w=writeWord (memoryView a) (passWord ord+2) (a.getReg .x31) w) := by
  have room := pass_word_room ord hj
  have ad : a.getReg .x29+signExtend12 16#12=wordAddress (passWord ord+2) := by
    rw [cur, show signExtend12 16#12=BitVec.ofNat 64 16 by decide, ← BitVec.ofNat_add]
    unfold wordAddress; congr 1; have := pass_word_mul ord; omega
  have ok : accessValid (wordAddress (passWord ord+2)) 8=true :=
    Opening.aligned_access (8*(passWord ord+2)) (by omega) (by unfold MEMORY_BYTES; omega)
  have smem : (walkRows a (postRows ph)).mem=(a.setMem (wordAddress (passWord ord+2)) (a.getReg .x31)).mem := by
    simp [postRows,walkRows,execInstrBr,ad,MachineState.setMem]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · interval_cases ph <;>
      simp [postRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,ad,ok,address]
  · interval_cases ph <;> simp [postRows,walkRows,execInstrBr,pc,address]
  · simp [postRows,walkRows,execInstrBr,show signExtend12 1024#12=1024#64 by decide]
  · simp [postRows,walkRows,execInstrBr,show signExtend12 1536#12=1536#64 by decide]
  · simp [postRows,walkRows,execInstrBr,show signExtend12 1#12=1#64 by decide]
  · intro k h10 h12 h13; simp [postRows,walkRows,execInstrBr,Ne.symm h10,Ne.symm h12,Ne.symm h13]
  · intro w hw
    change (walkRows a (postRows ph)).mem (wordAddress w)=_
    rw [smem]
    exact memory_at_store (state:=a) (address:=passWord ord+2) (index:=w) (value:=a.getReg .x31) (by omega) (by omega)

theorem called_pc (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (y : BitVec 1600) :
    (called s ord y).pc=address (3093+80*(ord%4)) := by
  rw [show (called s ord y).pc=(walkRows s (headRows (ord%4))).pc+4 from reply_pc ..,(head_run s i ord left r).2.1]
  exact address_step _ _ (by omega)

theorem called_reg (s : MachineState) (ord : Nat) (y : BitVec 1600) (x : Reg) :
    (called s ord y).getReg x=(walkRows s (headRows (ord%4))).getReg x := writeBits_register ..

/-- The memory after the inverse call: the reply in the 25 block words, the rest as at entry. -/
theorem called_view (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (hj : ord ≤ 16777216)
    (y : BitVec 1600) (w : Nat) (fit : w<2^33) :
    memoryView (called s ord y) w=if h : passWord ord≤w ∧ w<passWord ord+25 then
      replyWords y ⟨w-passWord ord,by omega⟩ else memoryView s w := by
  have room := pass_word_room ord hj
  change memoryView (writeBits (walkRows s (headRows (ord%4))) (wordAddress (passWord ord)) y) w=_
  rw [permutation_write_memory _ _ _ _ (by omega) fit,writeWindow]
  split
  · rfl
  · exact view_of_mem (head_run s i ord left r).2.2.1 w

/-- The registers after the head: the chain block's entry. -/
theorem headed_entry (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (hj : ord ≤ 16777216)
    (y : BitVec 1600) :
    ChainEntry (headed s ord y) i (ord%4) ∧ Registers (headed s ord y) ord left ∧
      (∀ k, k≠.x6 → k≠.x7 → k≠.x10 → k≠.x13 → k≠.x28 → k≠.x30 → k≠.x31 → k≠.x3 → (headed s ord y).getReg k=s.getReg k) ∧
      (∀ w, w<2^33 → memoryView (headed s ord y) w=writeWord (memoryView (called s ord y)) (passWord ord+2)
        (wordAddress (nodeWordOf (i.val/4^^^1))) w) := by
  unfold headed
  have hp : ord%4<4 := Nat.mod_lt _ (by decide)
  obtain ⟨_,_,_,_,t12,t13,t31,t6,_,_,t3,t30,tkeep⟩ := head_run s i ord left r
  have creg := called_reg s ord y
  obtain ⟨_,ppc,p10,p12,p13,pkeep,pview⟩ := post_run (called s ord y) ord (ord%4) hp (called_pc s i ord left r y)
    ((creg _).trans ((tkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans r.cursor)) hj
  set h := walkRows (called s ord y) (postRows (ord%4)) with hdef
  have k (x : Reg) (h10 : x≠.x10) (h12 : x≠.x12) (h13 : x≠.x13) : h.getReg x=(walkRows s (headRows (ord%4))).getReg x :=
    (pkeep x h10 h12 h13).trans (creg x)
  have kk (x : Reg) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide) (h10 : x≠.x10 := by decide)
      (h12 : x≠.x12 := by decide) (h13 : x≠.x13 := by decide) (h28 : x≠.x28 := by decide) (h30 : x≠.x30 := by decide)
      (h31 : x≠.x31 := by decide) (h3 : x≠.x3 := by decide) : h.getReg x=s.getReg x :=
    (k x h10 h12 h13).trans (tkeep x h6 h7 h10 h12 h13 h28 h30 h31 h3)
  have tab : TableAt h := by
    intro e he hh hh'
    have hi : i.val<16777216 := i.isLt
    have room := pass_word_room ord hj
    have fit : tableWord e+hh<2^33 := by simp only [tableWord]; omega
    rw [pview _ fit]
    simp only [writeWord, show tableWord e+hh≠passWord ord+2 by simp only [tableWord]; omega, if_false]
    rw [called_view s i ord left r hj y _ fit, dif_neg (by simp only [tableWord]; omega)]
    exact r.table e he hh hh'
  refine ⟨⟨hp,ppc,p10,p12,kk .x5 ▸ r.selector,kk .x11 ▸ r.width,p13,?_,?_,?_,tab⟩,
    ⟨p12,kk .x5 ▸ r.selector,kk .x11 ▸ r.width,p13,(kk .x14).trans r.index,(kk .x17).trans r.endReg,
      (by rw [kk .x25, r.shift, kk .x9]),(kk .x22).trans r.salt,(kk .x26).trans r.base⟩,?_,?_⟩
  · exact (k _ (by decide) (by decide) (by decide)).trans t6
  · exact (k _ (by decide) (by decide) (by decide)).trans t3
  · exact (k _ (by decide) (by decide) (by decide)).trans t30
  · intro x h6 h7 h10 h13 h28 h30 h31 h3
    by_cases h12 : x=.x12
    · subst h12; rw [p12]; exact r.output.symm
    · exact kk x h6 h7 h10 h12 h13 h28 h30 h31 h3
  · intro w hw
    rw [pview w hw, creg, t31]

/-! ### Salt rows and latch -/

def finish (t : MachineState) (ord left : Nat) : MachineState :=
  walkRows t (saltRows (ord%4)++latchRows (ord%4) (decide (left=1)))

def finalPC (ord left : Nat) := if left=1 then address 4096 else address (3079+80*((ord+1)%4))

/-- The salt source (`x28 = readAt i`, inside the chain reply) and destination (the block). -/
theorem salt_addresses (i : Index) (ord : Nat) (hj : ord ≤ 16777216) :
    accessValid (readAt i) 8=true ∧ accessValid (readAt i+8) 8=true ∧
    accessValid (wordAddress (passWord ord)) 8=true ∧ accessValid (wordAddress (passWord ord+1)) 8=true ∧
    readAt i+8≠wordAddress (passWord ord) := by
  have hi : i.val<16777216:=i.isLt
  have r : rank i.val<11 := by unfold rank;omega
  have off : offAt i<200 ∧ offAt i%8=0 := by unfold offAt;split_ifs <;> constructor <;> omega
  have room := pass_word_room ord hj
  have pb : proofBase=13824430176 := rfl
  unfold readAt wordAddress
  rw [show (8 : Word)=BitVec.ofNat 64 8 from rfl,←BitVec.ofNat_add]
  refine ⟨Opening.aligned_access _ (by omega) (by unfold MEMORY_BYTES; omega),
    Opening.aligned_access _ (by omega) (by unfold MEMORY_BYTES; omega),
    Opening.aligned_access _ (by omega) (by unfold MEMORY_BYTES; omega),
    Opening.aligned_access _ (by omega) (by unfold MEMORY_BYTES; omega),?_⟩
  intro eq
  have := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 1536+offAt i+8<2^64),
    Nat.mod_eq_of_lt (by omega : 8*passWord ord<2^64)] at this
  omega

/-- The block's salt words after the salt rows. -/
def saltInstalled (u : MachineState) (ord : Nat) (i : Index) : MachineState :=
  (u.setMem (wordAddress (passWord ord)) (u.getMem (readAt i))).setMem (wordAddress (passWord ord+1))
    (u.getMem (readAt i+8))

private theorem index_bump (ord : Nat) : indexAt ord+signExtend12 8=indexAt (ord+1) := by
  change BitVec.ofNat 64 _+BitVec.ofNat 64 8=_
  rw [←BitVec.ofNat_add];unfold indexAt;congr 1 <;> omega

private theorem index_inj (a b : Nat) (ha : a≤16777216) (hb : b≤16777216) : indexAt a=indexAt b ↔ a=b := by
  constructor
  · intro h
    have z:=congrArg BitVec.toNat h
    simp only [indexAt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 9395245088+8*a<2^64 by omega),
      Nat.mod_eq_of_lt (show 9395245088+8*b<2^64 by omega)] at z
    omega
  · intro h;rw [h]

private theorem z12 : signExtend12 0#12=0#64 := by decide
private theorem e12 : signExtend12 8#12=8#64 := by decide

/-- The table's salt source is the K1 reply address of the salt of `i`. -/
theorem tab_s_read (i : Index) : BitVec.ofNat 64 (tabS (i.val%4096))=readAt i := by
  unfold tabS tabOff readAt offAt rank
  congr 1

theorem stride_imm (ph : Nat) : signExtend12 (BitVec.ofNat 12 (passStride ph))=BitVec.ofNat 64 (passStride ph) := by
  unfold passStride; split <;> decide

/-- The latch (`addi x14,x14,8 ; bne x14,x17` and, after the last position, `addi x25,x9,0 ; jal <4096>`). -/
theorem latch_facts (v : MachineState) (ord left ph : Nat) (hph : ord%4=ph) (hp : ph<4) (l : 0<left)
    (bound : ord+left≤16777216) (pc : v.pc=address (3144+80*ph))
    (index : v.getReg .x14=indexAt ord) (endv : v.getReg .x17=indexAt (ord+left))
    (shift : v.getReg .x25=BitVec.ofNat 64 (8*(ord+left))) :
    let w:=walkRows v (latchRows ph (decide (left=1)))
    legal (latchRows ph (decide (left=1))) v ∧ w.pc=finalPC ord left ∧ w.getReg .x14=indexAt (ord+1) ∧
      w.getReg .x25=(if left-1=0 then v.getReg .x9 else BitVec.ofNat 64 (8*((ord+1)+(left-1)))) ∧
      w.mem=v.mem ∧ (∀ k, k≠.x14 → k≠.x25 → w.getReg k=v.getReg k) := by
  intro w
  set b:=execInstrBr v (.ADDI .x14 .x14 8) with hb
  have bpc : b.pc=address (3145+80*ph) := by
    rw [hb]; change v.pc+4=_; rw [pc]; exact address_step _ _ (by omega)
  have b14 : b.getReg .x14=indexAt (ord+1) := by
    rw [hb]; simp only [execInstrBr,MachineState.getReg_setPC,Opening.getReg_setReg,ite_true]
    rw [index]; exact index_bump ord
  have bk (k : Reg) (h : k≠.x14) : b.getReg k=v.getReg k := by simp [hb,execInstrBr,Ne.symm h]
  have bmem : b.mem=v.mem := by simp [hb,execInstrBr]
  have l0 : legal [(3144+80*ph,.ADDI .x14 .x14 8)] v := ⟨pc,rfl,trivial⟩
  by_cases last : left=1
  · have eql : b.getReg .x14=b.getReg .x17 := by
      rw [b14, bk _ (by decide), endv]; exact (index_inj _ _ (by omega) bound).mpr (by omega)
    have hd : decide (left=1)=true := decide_eq_true last
    have miss : execInstrBr b (.BNE .x14 .x17 (latchImm ph))=b.setPC (address (3146+80*ph)) := by
      have no : (b.getReg .x14 != b.getReg .x17)=false := by simp [eql]
      simp only [execInstrBr,no,Bool.false_eq_true,ite_false,bpc]
      exact congrArg b.setPC (address_step _ _ (by omega))
    set c:=b.setPC (address (3146+80*ph)) with hc
    have cstep : execInstrBr c (.ADDI .x25 .x9 0)=(c.setReg .x25 (c.getReg .x9)).setPC (address (3147+80*ph)) := by
      change (c.setReg .x25 (c.getReg .x9+signExtend12 0)).setPC (c.pc+4)=_
      rw [show c.pc=address (3146+80*ph) from rfl, address_step _ (3147+80*ph) (by omega)]
      simp [signExtend12]
    set d:=(c.setReg .x25 (c.getReg .x9)).setPC (address (3147+80*ph)) with hd'
    have dstep : execInstrBr d (.JAL .x0 (exitImm ph))=d.setPC (address 4096) := by
      change d.setPC (d.pc+signExtend21 (exitImm ph))=_
      rw [show d.pc=address (3147+80*ph) from rfl, exit_target ph hp]
    have wdef : w=d.setPC (address 4096) := by
      show walkRows v (latchRows ph (decide (left=1)))=_
      rw [hd]
      show execInstrBr (execInstrBr (execInstrBr b (.BNE .x14 .x17 (latchImm ph))) (.ADDI .x25 .x9 0))
        (.JAL .x0 (exitImm ph))=_
      rw [miss, cstep, dstep]
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [hd]
      refine ⟨pc,rfl,bpc,rfl,?_,rfl,?_,rfl,trivial⟩
      · rw [miss]; rfl
      · rw [miss, cstep]; rfl
    · rw [wdef]; unfold finalPC; rw [if_pos last]; rfl
    · rw [wdef]; simp [hd',hc]; exact b14
    · rw [wdef, if_pos (by omega)]; simp [hd',hc]; exact bk _ (by decide)
    · rw [wdef]; simp [hd',hc,bmem]
    · intro k h14 h25; rw [wdef]; simp [hd',hc,Ne.symm h25]; exact bk k h14
  · have neq : b.getReg .x14≠b.getReg .x17 := by
      rw [b14, bk _ (by decide), endv]
      intro h; exact last (by have := (index_inj _ _ (by omega) bound).mp h; omega)
    have hd : decide (left=1)=false := decide_eq_false last
    have hit : execInstrBr b (.BNE .x14 .x17 (latchImm ph))=b.setPC (address (3079+80*((ord+1)%4))) := by
      have yes : (b.getReg .x14 != b.getReg .x17)=true := by simp [neq]
      simp only [execInstrBr,yes,ite_true,bpc]
      rw [latch_target ph hp, show (ph+1)%4=(ord+1)%4 by omega]
    have wdef : w=b.setPC (address (3079+80*((ord+1)%4))) := by
      show walkRows v (latchRows ph (decide (left=1)))=_
      rw [hd]
      show execInstrBr b (.BNE .x14 .x17 (latchImm ph))=_
      exact hit
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [hd]; exact ⟨pc,rfl,bpc,rfl,trivial⟩
    · rw [wdef]; unfold finalPC; rw [if_neg last]; rfl
    · rw [wdef]; simp; exact b14
    · rw [wdef, if_neg (by omega)]; simp; rw [bk _ (by decide), shift]; congr 2; omega
    · rw [wdef]; exact bmem
    · intro k h14 _; rw [wdef]; simp; exact bk k h14

/-- The salt rows and the latch, from the end of the link block (`3139+80ph`). -/
theorem finish_facts (u : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (bound : ord+left≤16777216)
    (pc : u.pc=address (3139+80*(ord%4))) (regs : Registers u ord left) (src : u.getReg .x28=readAt i)
    (cur : u.getReg .x29=BitVec.ofNat 64 (passDest ord)) :
    let t:=finish u ord left
    legal (saltRows (ord%4)++latchRows (ord%4) (decide (left=1))) u ∧
      Registers t (ord+1) (left-1) ∧ t.pc=finalPC ord left ∧
      t.getReg .x29=BitVec.ofNat 64 (passDest (ord+1)) ∧ t.mem=(saltInstalled u ord i).mem ∧
      (∀ k, k≠.x29 → k≠.x31 → k≠.x14 → k≠.x25 → t.getReg k=u.getReg k) := by
  intro t
  obtain ⟨ph,hph⟩ : ∃ ph, ord%4=ph := ⟨_,rfl⟩
  have hp : ph<4 := hph ▸ Nat.mod_lt _ (by decide)
  rw [hph] at pc
  obtain ⟨a0,a8,d0,d1,ne⟩ := salt_addresses i ord (by omega)
  have d1' : u.getReg .x29+signExtend12 8#12=wordAddress (passWord ord+1) := by
    rw [cur, e12, show (8#64 : Word)=BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
    unfold wordAddress; congr 1; have := pass_word_mul ord; omega
  have d0' : u.getReg .x29+signExtend12 0#12=wordAddress (passWord ord) := by
    rw [cur, z12, BitVec.add_zero, pass_word_address]
  have s8 : u.getReg .x28+signExtend12 8#12=readAt i+8 := by rw [src, e12]; rfl
  have s0 : u.getReg .x28+signExtend12 0#12=readAt i := by rw [src, z12, BitVec.add_zero]
  have a8' : accessValid (readAt i+8#64) 8=true := a8
  have ne' : readAt i+8#64≠wordAddress (passWord ord) := ne
  set v:=walkRows u (saltRows ph) with hv
  have tdef : t=walkRows v (latchRows ph (decide (left=1))) := by
    show walkRows u (saltRows (ord%4)++latchRows (ord%4) _)=_; rw [hph, walk_join]
  have vpc : v.pc=address (3144+80*ph) := by
    interval_cases ph <;> simp [hv,saltRows,walkRows,execInstrBr,pc,address]
  have vmem : v.mem=(saltInstalled u ord i).mem := by
    simp [hv,saltRows,walkRows,execInstrBr,saltInstalled,MachineState.getMem_setMem_ne ne',mem_of_store,s0,s8,d0',d1']
  have v29 : v.getReg .x29=BitVec.ofNat 64 (passDest (ord+1)) := by
    simp only [hv,saltRows,walkRows,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
      Opening.getReg_setReg,Opening.getReg_setMem,ite_true]
    simp [stride_imm, cur, ← BitVec.ofNat_add, ← pass_dest_next, hph]
  have vkeep (k : Reg) (h29 : k≠.x29) (h31 : k≠.x31) : v.getReg k=u.getReg k := by
    simp [hv,saltRows,walkRows,execInstrBr,Ne.symm h29,Ne.symm h31]
  have vlegal : legal (saltRows ph) u := by
    interval_cases ph <;>
    · simp [saltRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,address,a0,a8,a8',d0,d1,
        s0,s8,d0',d1']
      all_goals first | exact ⟨d1,ne⟩ | decide | skip
  obtain ⟨ll,lpc,l14,l25,lmem,lkeep⟩ := latch_facts v ord left ph hph hp l bound vpc
    ((vkeep _ (by decide) (by decide)).trans regs.index) ((vkeep _ (by decide) (by decide)).trans regs.endReg)
    (by rw [vkeep _ (by decide) (by decide), regs.shift]; simp [show left≠0 by omega])
  have tk (k : Reg) (h29 : k≠.x29) (h31 : k≠.x31) (h14 : k≠.x14) (h25 : k≠.x25) : t.getReg k=u.getReg k := by
    rw [tdef, lkeep k h14 h25, vkeep k h29 h31]
  refine ⟨?_,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,tk⟩
  · rw [hph]; exact legal_append _ _ _ vlegal ll
  · exact (tk _ (by decide) (by decide) (by decide) (by decide)).trans regs.output
  · exact (tk _ (by decide) (by decide) (by decide) (by decide)).trans regs.selector
  · exact (tk _ (by decide) (by decide) (by decide) (by decide)).trans regs.width
  · exact (tk _ (by decide) (by decide) (by decide) (by decide)).trans regs.primitive
  · rw [tdef]; exact l14
  · rw [tk _ (by decide) (by decide) (by decide) (by decide), regs.endReg, show ord+1+(left-1)=ord+left by omega]
  · rw [tdef, l25, lkeep .x9 (by decide) (by decide)]
  · exact (tk _ (by decide) (by decide) (by decide) (by decide)).trans regs.salt
  · exact (tk _ (by decide) (by decide) (by decide) (by decide)).trans regs.base
  · rw [tdef]; exact lpc
  · rw [tdef, lkeep _ (by decide) (by decide)]; exact v29
  · rw [tdef, lmem]; exact vmem

/-! ### One position -/

/-- The inverse query: the quartet's 200-byte reply in the trapdoor (the table entry's reply offset). -/
def inverseQuery (s : MachineState) (i : Index) : BitVec 1600 :=
  packBuffer (window (memoryView s) (replyWord (i.val/4)))

def perTrace (s : MachineState) (i : Index) (ord left : Nat) : OracleComp World MachineState := do
  let y ← World.query (.inr (.inr (.inr (inverseQuery s i))))
  let t ← chainTrace (headed s ord y) i (ord%4)
  return finish t ord left

def perSteps (i : Index) (left : Nat) := 18+(chainSteps i+(7+2*(if left=1 then 1 else 0)))
def perCycles (i : Index) (left : Nat) := 25+(chainCycles i+(7+2*(if left=1 then 1 else 0)))
def perCalls (i : Index) := 1+chainCalls i

theorem present_append {a b : List Row} (ha : presentRows a) (hb : presentRows b) : presentRows (a++b) :=
  fun p hp => (List.mem_append.mp hp).elim (ha p) (hb p)

private theorem charge_comm (e : Execution) (a b c d : Nat) :
    (e.charge a c).charge b d=e.charge (b+a) (d+c) := by
  cases e; simp [Execution.charge,Nat.add_assoc]

/-- The registers the chain leaves for the salt rows. -/
theorem chain_regs (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (hj : ord ≤ 16777216)
    (y : BitVec 1600) (t : MachineState) (hit : t ∈ support (chainTrace (headed s ord y) i (ord%4))) :
    t.pc=address (3139+80*(ord%4)) ∧ Registers t ord left ∧ t.getReg .x28=readAt i ∧
      t.getReg .x29=BitVec.ofNat 64 (passDest ord) ∧
      (∀ k, k≠.x3 → k≠.x6 → k≠.x7 → k≠.x10 → k≠.x13 → k≠.x28 → k≠.x30 → k≠.x31 → t.getReg k=s.getReg k) ∧
      (∀ w, w<2^33 → w≠128 → (w<192 ∨ 217≤w) → memoryView t w=memoryView (headed s ord y) w) := by
  obtain ⟨ent,hregs,hkeep,_⟩ := headed_entry s i ord left r hj y
  obtain ⟨tpc,t28,_,tkeep,tview⟩ := chain_post _ i (ord%4) ent t hit
  have tk (x : Reg) (h3 : x≠.x3 := by decide) (h7 : x≠.x7 := by decide) (h10 : x≠.x10 := by decide)
      (h28 : x≠.x28 := by decide) (h30 : x≠.x30 := by decide) (h31 : x≠.x31 := by decide) :=
    tkeep x h3 h7 h10 h28 h30 h31
  refine ⟨tpc,⟨(tk .x12).trans hregs.output,(tk .x5).trans hregs.selector,(tk .x11).trans hregs.width,
    (tk .x13).trans hregs.primitive,(tk .x14).trans hregs.index,(tk .x17).trans hregs.endReg,
    (by rw [tk .x25, hregs.shift, tk .x9]),(tk .x22).trans hregs.salt,(tk .x26).trans hregs.base⟩,
    t28.trans (tab_s_read i),?_,?_,tview⟩
  · rw [tk .x29, hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact r.cursor
  · intro k h3 h6 h7 h10 h13 h28 h30 h31
    rw [tkeep k h3 h7 h10 h28 h30 h31]; exact hkeep k h6 h7 h10 h13 h28 h30 h31 h3

/-- One position: its head, the inverse call, the chained generator, the salt rows and the latch. -/
theorem per_run (s : MachineState) (i : Index) (ord left fuel : Nat) (l : 0<left) (bound : ord+left≤16777216)
    (r : Entry s i ord left) : execute openingImage (perSteps i left+fuel) s true =
      (do let t ← perTrace s i ord left; let z ← execute openingImage fuel t true
          return z.charge (perCycles i left) (perCalls i)) := by
  have hj : ord ≤ 16777216 := by omega
  have hp : ord%4<4 := Nat.mod_lt _ (by decide)
  obtain ⟨l1,apc,amem,a10,a12,a13,_,_,_,_,_,_,akeep⟩ := head_run s i ord left r
  have k (x : Reg) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide) (h10 : x≠.x10 := by decide)
      (h12 : x≠.x12 := by decide) (h13 : x≠.x13 := by decide) (h28 : x≠.x28 := by decide)
      (h30 : x≠.x30 := by decide) (h31 : x≠.x31 := by decide) (h3 : x≠.x3 := by decide) :=
    akeep x h6 h7 h10 h12 h13 h28 h30 h31 h3
  have room := pass_word_room ord hj
  have hix : i.val<16777216 := i.isLt
  have src : replyWord (i.val/4)+25≤2^33 := by unfold replyWord blockWord; omega
  have dst : passWord ord+25≤2^33 := by omega
  have lens := row_lengths (ord%4)
  have ll := latch_lengths (ord%4) (decide (left=1))
  have fl : (saltRows (ord%4)++latchRows (ord%4) (decide (left=1))).length=7+2*(if left=1 then 1 else 0) := by
    rw [List.length_append, lens.2.2.2.2.1, ll.1]; by_cases h : left=1 <;> simp [h]
  have fp : price (saltRows (ord%4)++latchRows (ord%4) (decide (left=1)))=7+2*(if left=1 then 1 else 0) := by
    rw [price_append, lens.2.2.2.2.2, ll.2]; by_cases h : left=1 <;> simp [h]
  rw [show perSteps i left+fuel=(headRows (ord%4)).length+(((postRows (ord%4)).length+(chainSteps i+
      ((saltRows (ord%4)++latchRows (ord%4) (decide (left=1))).length+fuel)))+1) by
      unfold perSteps; rw [lens.1, lens.2.2.1, fl]; omega,
    walk_rows_run s _ l1 (head_fetch _ hp) _ true,
    execute_inverse_call openingImage _ (walkRows s (headRows (ord%4))) true (replyWord (i.val/4)) (passWord ord)
      src dst a10 a12 ((k .x5).trans r.selector) ((k .x11).trans r.width) a13 (inverse_fetch _ _ hp apc)]
  have qeq : packBuffer (window (memoryView (walkRows s (headRows (ord%4)))) (replyWord (i.val/4)))=
      inverseQuery s i := by
    unfold inverseQuery; rw [show memoryView (walkRows s (headRows (ord%4)))=memoryView s from funext (view_of_mem amem)]
  rw [qeq]
  simp only [perTrace,bind_assoc,pure_bind]
  apply bind_congr; intro y
  have creg := called_reg s ord y
  have pl : legal (postRows (ord%4)) (called s ord y) :=
    (post_run _ ord _ hp (called_pc s i ord left r y) ((creg _).trans ((k .x29).trans r.cursor)) hj).1
  rw [show writeBits (walkRows s (headRows (ord%4))) (wordAddress (passWord ord)) y=called s ord y from rfl,
    walk_rows_run _ (postRows (ord%4)) pl (post_fetch _ hp) _ true,
    show walkRows (called s ord y) (postRows (ord%4))=headed s ord y from rfl,
    chain_run _ i (ord%4) (headed_entry s i ord left r hj y).1]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support; intro t hit
  obtain ⟨tpc,tregs,t28,t29,_,_⟩ := chain_regs s i ord left r hj y t hit
  have fin := finish_facts t i ord left l bound tpc tregs t28 t29
  rw [walk_rows_run t _ fin.1 (present_append (salt_fetch _ hp) (latch_fetch _ hp _)) fuel true]
  simp only [bind_assoc,pure_bind]
  apply bind_congr; intro e; apply congrArg pure
  rw [charge_comm, charge_comm, charge_comm, charge_comm, fp, lens.2.1, lens.2.2.2.1]
  unfold perCycles perCalls
  congr 1 <;> omega

/-- Words a position may write: the generator counter (128), the scratch reply, its block's 25 words. -/
def Writes (ord : Nat) (w : Nat) : Prop := w=128 ∨ (192≤w ∧ w<217) ∨ (passWord ord≤w ∧ w<passWord ord+25)

/-- Registers a position keeps. -/
def Saved (r : Reg) := r≠.x3 ∧ r≠.x6 ∧ r≠.x7 ∧ r≠.x10 ∧ r≠.x12 ∧ r≠.x13 ∧ r≠.x14 ∧ r≠.x25 ∧ r≠.x28 ∧ r≠.x29 ∧
  r≠.x30 ∧ r≠.x31

/-- The salt words land in the block's first two words, the rest of the memory as before them. -/
theorem salt_view (u : MachineState) (ord : Nat) (i : Index) (hj : ord ≤ 16777216) (w : Nat) (fit : w<2^33)
    (apart : w≠passWord ord ∧ w≠passWord ord+1) : memoryView (saltInstalled u ord i) w=memoryView u w := by
  have room := pass_word_room ord hj
  have distinct (v : Nat) (hv : v<2^33) (ne : w≠v) : wordAddress w≠wordAddress v :=
    fun h => ne (wordAddress_injective_of_bound (by omega) (by omega) h)
  change (saltInstalled u ord i).getMem (wordAddress w)=_
  rw [saltInstalled,MachineState.getMem_setMem_ne (distinct _ (by omega) apart.2),
    MachineState.getMem_setMem_ne (distinct _ (by omega) apart.1)]; rfl

theorem salt_words_at (u : MachineState) (ord : Nat) (i : Index) (hj : ord ≤ 16777216) (j : Fin 2) :
    memoryView (saltInstalled u ord i) (passWord ord+j.val)=u.getMem (readAt i+BitVec.ofNat 64 (8*j.val)) := by
  have room := pass_word_room ord hj
  have ne : wordAddress (passWord ord+1)≠wordAddress (passWord ord) :=
    fun h => (by have := wordAddress_injective_of_bound (by omega) (by omega) h; omega : False)
  change (saltInstalled u ord i).getMem (wordAddress (passWord ord+j.val))=_
  fin_cases j
  · simp only [saltInstalled, Fin.zero_eta, Fin.val_zero, Nat.add_zero, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero]
    rw [MachineState.getMem_setMem_ne (Ne.symm ne), MachineState.getMem_setMem_eq]
  · simp only [saltInstalled, MachineState.getMem_setMem_eq]
    congr 1

theorem trace_post (s : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (bound : ord+left≤16777216)
    (r : Entry s i ord left) (t : MachineState) (hit : t ∈ support (perTrace s i ord left)) :
    Registers t (ord+1) (left-1) ∧ t.pc=finalPC ord left ∧ t.getReg .x29=BitVec.ofNat 64 (passDest (ord+1)) ∧
      (∀ k, Saved k → t.getReg k=s.getReg k) ∧
      (∀ w, w<2^33 → ¬Writes ord w → memoryView t w=memoryView s w) ∧
      memoryView t (passWord ord+2)=wordAddress (nodeWordOf (i.val/4^^^1)) := by
  have hj : ord ≤ 16777216 := by omega
  have room := pass_word_room ord hj
  have pb : proofBase=13824430176 := rfl
  simp only [perTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨y,_,u,hu,rfl⟩ := hit
  obtain ⟨upc,uregs,u28,u29,ukeep,uview⟩ := chain_regs s i ord left r hj y u hu
  obtain ⟨_,fregs,fpc,f29,fmem,fkeep⟩ := finish_facts u i ord left l bound upc uregs u28 u29
  obtain ⟨_,_,_,hview⟩ := headed_entry s i ord left r hj y
  have tv (w : Nat) (fit : w<2^33) (apart : w≠passWord ord ∧ w≠passWord ord+1) :
      memoryView (finish u ord left) w=memoryView u w :=
    (view_of_mem fmem w).trans (salt_view u ord i hj w fit apart)
  refine ⟨fregs,fpc,f29,?_,?_,?_⟩
  · intro k ⟨h3,h6,h7,h10,h12,h13,h14,h25,h28,h29,h30,h31⟩
    rw [fkeep k h29 h31 h14 h25]; exact ukeep k h3 h6 h7 h10 h13 h28 h30 h31
  · intro w fit away
    have n128 : w≠128 := fun h => away (Or.inl h)
    have nsc : w<192 ∨ 217≤w := by by_contra h; exact away (Or.inr (Or.inl (by omega)))
    have nb : w<passWord ord ∨ passWord ord+25≤w := by by_contra h; exact away (Or.inr (Or.inr (by omega)))
    rw [tv w fit (by omega), uview w fit n128 nsc, hview w fit]
    simp only [writeWord, show w≠passWord ord+2 by omega, if_false]
    rw [called_view s i ord left r hj y w fit, dif_neg (by omega)]
  · rw [tv _ (by omega) (by omega), uview _ (by omega) (by omega) (Or.inr (by omega)), hview _ (by omega)]
    simp [writeWord]

/-! ### Fixed oracle -/

noncomputable def fixedInverse (o : Oracle) (s : MachineState) (i : Index) : BitVec 1600 :=
  o.permutation.symm (inverseQuery s i)
noncomputable def fixedHead (o : Oracle) (s : MachineState) (i : Index) (ord : Nat) : MachineState :=
  headed s ord (fixedInverse o s i)
noncomputable def fixedOne (o : Oracle) (s : MachineState) (i : Index) (ord left : Nat) : MachineState :=
  finish (chainState o (fixedHead o s i ord) i (ord%4)) ord left

theorem head_keys (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (hj : ord ≤ 16777216)
    (y : BitVec 1600) (k : BitVec 192) (key : KeyWords s k) : KeyWords (headed s ord y) k := by
  have room := pass_word_room ord hj
  have pb : proofBase=13824430176 := rfl
  intro j lo hi
  obtain ⟨_,_,_,hview⟩ := headed_entry s i ord left r hj y
  rw [hview _ (by omega)]
  simp only [writeWord, show 128+j≠passWord ord+2 by omega, if_false]
  rw [called_view s i ord left r hj y _ (by omega), dif_neg (by omega)]
  exact key j lo hi

theorem chain_state_support (o : Oracle) (k : BitVec 192) (h : MachineState) (i : Index) (ph : Nat)
    (e : ChainEntry h i ph) (key : KeyWords h k) : chainState o h i ph ∈ support (chainTrace h i ph) := by
  have h1 := chain_fixed o k h i ph e key
  unfold Oracle.run at h1
  exact writer_support (o.world.withAddCost Oracle.callCost) _ (chainState o h i ph,chainCalls i)
    (by rw [h1]; exact Set.mem_singleton _)

theorem trace_fixed (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left : Nat)
    (r : Entry s i ord left) (hj : ord ≤ 16777216) (key : KeyWords s k) :
    o.run (perTrace s i ord left)=pure (fixedOne o s i ord left,perCalls i) := by
  have helper (y : BitVec 1600) : o.run (do let t ← chainTrace (headed s ord y) i (ord%4); return finish t ord left)=
      pure (finish (chainState o (headed s ord y) i (ord%4)) ord left,chainCalls i) := by
    rw [oracle_run_bind,chain_fixed o k _ i _ (headed_entry s i ord left r hj y).1 (head_keys s i ord left r hj y k key)]
    simp [oracle_run_pure]
  unfold perTrace fixedOne fixedHead perCalls
  rw [oracle_run_public_bind]
  simp only [Oracle.answer]
  erw [helper (o.permutation.symm (inverseQuery s i))]
  simp [fixedInverse,Nat.add_comm]

theorem fixed_mem (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left : Nat)
    (r : Entry s i ord left) (hj : ord ≤ 16777216) (key : KeyWords s k) :
    fixedOne o s i ord left ∈ support (perTrace s i ord left) := by
  unfold fixedOne fixedHead perTrace
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff]
  exact ⟨fixedInverse o s i,mem_support_query _ _,_,chain_state_support o k _ i _
    (headed_entry s i ord left r hj _).1 (head_keys s i ord left r hj _ k key),rfl⟩

def selectedWord (i : Index) (j : Fin 2) := saltSlot (coord i).2+j.val

theorem slot_offset (i : Index) : 8*saltSlot (coord i).2=offAt i := by
  have c : (coord i).2.val=rank i.val := rfl
  have rh : rank i.val<11 := by unfold rank;omega
  unfold saltSlot offAt;rw [c];split_ifs <;> omega

theorem salt_read (u : MachineState) (i : Index) (j : Fin 2) :
    u.getMem (readAt i+BitVec.ofNat 64 (8*j.val))=memoryView u (192+selectedWord i j) := by
  have jj:=j.isLt
  have a : readAt i+BitVec.ofNat 64 (8*j.val)=wordAddress (192+selectedWord i j) := by
    unfold readAt wordAddress;rw [←BitVec.ofNat_add,←slot_offset];unfold selectedWord
    congr 1;omega
  rw [a]; rfl

/-- The fixed outcome's block: the linked salt in words 0..1, the pointer in word 2, the inverse reply's words
3..24. -/
theorem fixed_block (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left : Nat)
    (l : 0<left) (bound : ord+left≤16777216) (r : Entry s i ord left) (key : KeyWords s k) :
    (∀ j : Fin 2, memoryView (fixedOne o s i ord left) (passWord ord+j.val)=
      saltWords (Permutation.LinkedSalt.salts (Permutation.LinkedSalt.schedule Permutation.LinkedSalt.period)
        o.permutation k i) j) ∧
    (∀ m (hm : m<25), 3≤m → memoryView (fixedOne o s i ord left) (passWord ord+m)=
      replyWords (fixedInverse o s i) ⟨m,hm⟩) := by
  have hj : ord ≤ 16777216 := by omega
  have room := pass_word_room ord hj
  have pb : proofBase=13824430176 := rfl
  have ent := headed_entry s i ord left r hj (fixedInverse o s i)
  have hk := head_keys s i ord left r hj (fixedInverse o s i) k key
  have mem := chain_state_support o k _ i _ ent.1 hk
  obtain ⟨upc,uregs,u28,u29,_,uview⟩ := chain_regs s i ord left r hj _ _ mem
  obtain ⟨_,_,_,_,fmem,_⟩ := finish_facts _ i ord left l bound upc uregs u28 u29
  constructor
  · intro j
    have jj := j.isLt
    have sel : selectedWord i j<25 := by have:=salt_slot_bound (coord i).2;unfold selectedWord;omega
    unfold fixedOne fixedHead
    rw [view_of_mem fmem, salt_words_at _ ord i hj j, salt_read, chain_reply o k _ i _ ent.1 hk ⟨selectedWord i j,sel⟩]
    exact congrFun (salt_slice_eq (chainReply o k i) (coord i).2) j
  · intro m hm three
    unfold fixedOne fixedHead
    rw [view_of_mem fmem, salt_view _ ord i hj _ (by omega) (by omega),
      uview _ (by omega) (by omega) (Or.inr (by omega)), ent.2.2.2 _ (by omega)]
    simp only [writeWord, show passWord ord+m≠passWord ord+2 by omega, if_false]
    rw [called_view s i ord left r hj _ _ (by omega), dif_pos (by omega)]
    congr 1; apply Fin.ext; simp

end TwoPermutationPrototype.GroupedOpening.Layout2V2
