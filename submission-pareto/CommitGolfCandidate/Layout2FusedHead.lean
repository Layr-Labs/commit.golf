import CommitGolfCandidate.Layout2FusedRows

/-! Fused opener, one position: the loop registers, the head rows, the inverse call into the record block and the chain's
entry and exit registers. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2F
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolfCandidate.Layout2Phase (stride)
open CommitGolfCandidate.Permutation.CounterSalt (coord)
open TwoPermutationPrototype.Sampling (saltWords)
open TwoPermutationPrototype.GroupedOpening.Layout2V2 (linkedSalts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

/-! ### Registers -/

/-- Registers the loop keeps between positions (ordinal `ord`, `left` positions to go). -/
structure Regs (s : MachineState) (ord left : Nat) : Prop where
  output : s.getReg .x12=1536
  selector : s.getReg .x5=0
  width : s.getReg .x11=200
  primitive : s.getReg .x13=1
  index : s.getReg .x8=indexAt ord
  endReg : s.getReg .x17=indexAt (ord+left)
  salt : s.getReg .x22=9126809632
  base : s.getReg .x26=4096
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  capHeap : s.getReg .x25=BitVec.ofNat 64 trapdoorBase
  leaves : s.getReg .x19=4194304
  start : s.getReg .x20=BitVec.ofNat 64 proofBase
  mark : s.getReg .x23=1
  slots : s.getReg .x24=BitVec.ofNat 64 groupSlots
  capLeaves : s.getReg .x27=256
  sp : s.getReg .x2=BitVec.ofNat 64 tableBase
  mask : s.getReg .x1=65535

/-- Registers a whole position keeps. -/
def Saved (r : Reg) := r≠.x3 ∧ r≠.x4 ∧ r≠.x6 ∧ r≠.x7 ∧ r≠.x8 ∧ r≠.x10 ∧ r≠.x12 ∧ r≠.x13 ∧ r≠.x18 ∧ r≠.x21 ∧
  r≠.x28 ∧ r≠.x30 ∧ r≠.x31
instance (r : Reg) : Decidable (Saved r) := by unfold Saved; infer_instance

theorem regs_of_saved {s t : MachineState} {ord left : Nat} (r : Regs s ord left)
    (keep : ∀ k, Saved k → t.getReg k=s.getReg k) (x12 : t.getReg .x12=1536) (x13 : t.getReg .x13=1)
    (x8 : t.getReg .x8=indexAt (ord+1)) (pos : 0<left) : Regs t (ord+1) (left-1) := by
  have k (x : Reg) (h : Saved x := by unfold Saved; decide) := keep x h
  exact ⟨x12,(k .x5).trans r.selector,(k .x11).trans r.width,x13,x8,
    by rw [k .x17, r.endReg, show ord+1+(left-1)=ord+left by omega],(k .x22).trans r.salt,(k .x26).trans r.base,
    (k .x9).trans r.heap,(k .x25).trans r.capHeap,(k .x19).trans r.leaves,(k .x20).trans r.start,
    (k .x23).trans r.mark,(k .x24).trans r.slots,(k .x27).trans r.capLeaves,(k .x2).trans r.sp,(k .x1).trans r.mask⟩

/-- Entry of position `i` at ordinal `ord` (`left` to go). -/
structure Entry (s : MachineState) (i : Index) (ord left : Nat) extends Regs s ord left where
  pc : s.pc=address (4097+272*(ord%4))
  cursor : s.getReg .x21=BitVec.ofNat 64 (destOf ord)
  loaded : s.getMem (indexAt ord)=BitVec.ofNat 64 i.val
  access : accessValid (indexAt ord) 8=true
  table : TableAt s

private theorem load_ok (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) :
    memoryArgumentsValid s (.LD .x6 .x8 0)=true := by
  simpa [memoryArgumentsValid,memAccess,r.index,show signExtend12 0#12=0#64 by decide] using r.access

/-! ### Head: rows `4097+272ph .. 4109+272ph` -/

private def headA (ph : Nat) : List Row := [(4097+272*ph,.LD .x6 .x8 0),(4098+272*ph,.SRLI .x28 .x6 2),
  (4099+272*ph,.SLLI .x3 .x6 4),(4100+272*ph,.AND .x30 .x3 .x1),(4101+272*ph,.ADD .x30 .x30 .x2)]
private def headB (ph : Nat) : List Row := [(4102+272*ph,.SLLI .x7 .x28 10),(4103+272*ph,.ADD .x7 .x7 .x24),
  (4104+272*ph,.ADDI .x12 .x21 0)]
private def headC (ph : Nat) : List Row := [(4105+272*ph,.LH .x10 .x30 4),(4106+272*ph,.ADD .x10 .x10 .x7),
  (4107+272*ph,.LH .x18 .x30 6),(4108+272*ph,.ADD .x18 .x18 .x7),(4109+272*ph,.ADDI .x13 .x0 2)]
private theorem head_split (ph : Nat) : headRows ph=headA ph++headB ph++headC ph := rfl

private theorem head_a (s : MachineState) (i : Index) (ord left ph : Nat) (hph : ord%4=ph) (hp : ph<4)
    (r : Entry s i ord left) :
    let t:=walkRows s (headA ph)
    legal (headA ph) s ∧ t.pc=address (4102+272*ph) ∧ t.mem=s.mem ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
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

private theorem head_b (a : MachineState) (i : Index) (ph : Nat) (hp : ph<4) (pc : a.pc=address (4102+272*ph))
    (x28 : a.getReg .x28=BitVec.ofNat 64 (i.val/4)) (slots : a.getReg .x24=BitVec.ofNat 64 groupSlots) :
    let b:=walkRows a (headB ph)
    legal (headB ph) a ∧ b.pc=address (4105+272*ph) ∧ b.mem=a.mem ∧
      b.getReg .x7=wordAddress (blockWord (i.val/4)) ∧ b.getReg .x12=a.getReg .x21 ∧
      (∀ k, k≠.x7 → k≠.x12 → b.getReg k=a.getReg k) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · interval_cases ph <;> exact legal_of_chain _ _ (by decide) (by simp [headB,pcChain,execInstrBr,pc,address])
  · interval_cases ph <;> simp [headB,walkRows,execInstrBr,pc,address]
  · simp [headB,walkRows,execInstrBr]
  · simp [headB,walkRows,execInstrBr]
    rw [x28, slots]; exact block_value i
  · simp [headB,walkRows,execInstrBr,show signExtend12 0#12=0#64 by decide]
  · intro k h7 h12; simp [headB,walkRows,execInstrBr,Ne.symm h7,Ne.symm h12]

private theorem head_c (c : MachineState) (i : Index) (ph : Nat) (hp : ph<4) (pc : c.pc=address (4105+272*ph))
    (x30 : c.getReg .x30=wordAddress (tableWord (i.val%4096))) (x7 : c.getReg .x7=wordAddress (blockWord (i.val/4)))
    (tab : TableAt c) :
    let d:=walkRows c (headC ph)
    legal (headC ph) c ∧ d.pc=address (4110+272*ph) ∧ d.mem=c.mem ∧
      d.getReg .x10=wordAddress (replyWord (i.val/4)) ∧ d.getReg .x18=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      d.getReg .x13=2 ∧ (∀ k, k≠.x10 → k≠.x18 → k≠.x13 → d.getReg k=c.getReg k) := by
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
  · have e1 : (walkRows c (headC ph)).getReg .x18=
        (c.getHalfword (c.getReg .x30+signExtend12 6#12)).signExtend 64+c.getReg .x7 := rfl
    rw [e1, x30, hG, x7]; exact node_offset i
  · simp [headC,walkRows,execInstrBr,show signExtend12 2#12=2#64 by decide]
  · intro k h10 h18 h13; simp [headC,walkRows,execInstrBr,Ne.symm h10,Ne.symm h18,Ne.symm h13]

/-- The head rows: the reply address in `x10`, the block in `x12`, the L22 node's address in `x18`. -/
theorem head_run (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) :
    let ph:=ord%4
    let t:=walkRows s (headRows ph)
    legal (headRows ph) s ∧ t.pc=address (4110+272*ph) ∧ t.mem=s.mem ∧
      t.getReg .x10=wordAddress (replyWord (i.val/4)) ∧ t.getReg .x12=wordAddress (blockW ord) ∧
      t.getReg .x13=2 ∧ t.getReg .x18=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      t.getReg .x6=BitVec.ofNat 64 i.val ∧ t.getReg .x28=BitVec.ofNat 64 (i.val/4) ∧
      t.getReg .x7=wordAddress (blockWord (i.val/4)) ∧
      t.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) ∧ t.getReg .x30=wordAddress (tableWord (i.val%4096)) ∧
      (∀ k, k≠.x6 → k≠.x7 → k≠.x10 → k≠.x12 → k≠.x13 → k≠.x28 → k≠.x30 → k≠.x18 → k≠.x3 →
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
  obtain ⟨lc,cpc,cmem,c10,c18,c13,ckeep⟩ := head_c b i ph hp bpc
    ((bkeep _ (by decide) (by decide)).trans a30) b7 btab
  have at_t : t=walkRows b (headC ph) := by
    show walkRows s (headRows ph)=_; rw [head_split, walk_join, walk_join]
  have kb (k : Reg) (h7 : k≠.x7) (h12 : k≠.x12) (h10 : k≠.x10) (h18 : k≠.x18) (h13 : k≠.x13) :
      t.getReg k=a.getReg k := by rw [at_t, ckeep k h10 h18 h13, bkeep k h7 h12]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [head_split]; exact legal_append _ _ _ (legal_append _ _ _ la lb) (by rw [walk_join]; exact lc)
  · rw [at_t]; exact cpc
  · rw [at_t, cmem, bmem]; exact amem
  · rw [at_t]; exact c10
  · rw [at_t, ckeep _ (by decide) (by decide) (by decide), b12,
      akeep _ (by decide) (by decide) (by decide) (by decide), r.cursor, block_address]
  · rw [at_t]; exact c13
  · rw [at_t]; exact c18
  · rw [kb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a6
  · rw [kb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a28
  · rw [at_t, ckeep _ (by decide) (by decide) (by decide)]; exact b7
  · rw [kb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a3
  · rw [kb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a30
  · intro k h6 h7 h10 h12 h13 h28 h30 h18 h3
    rw [kb k h7 h12 h10 h18 h13]; exact akeep k h6 h28 h3 h30

/-! ### After the inverse call: rows `4111+272ph .. 4113+272ph` -/

/-- The state after the inverse call wrote `y` to the block. -/
def called (s : MachineState) (ord : Nat) (y : BitVec 1600) : MachineState :=
  writeBits (walkRows s (headRows (ord%4))) (wordAddress (blockW ord)) y

/-- The head of a position: rows, the inverse reply `y` at the block, the generator input registers. -/
def headed (s : MachineState) (ord : Nat) (y : BitVec 1600) : MachineState :=
  walkRows (called s ord y) (postRows (ord%4))

theorem post_run (a : MachineState) (ph : Nat) (hp : ph<4) (pc : a.pc=address (4111+272*ph)) :
    let t:=walkRows a (postRows ph)
    legal (postRows ph) a ∧ t.pc=address (4114+272*ph) ∧ t.getReg .x10=1024 ∧ t.getReg .x12=1536 ∧
      t.getReg .x13=1 ∧ (∀ k, k≠.x10 → k≠.x12 → k≠.x13 → t.getReg k=a.getReg k) ∧ t.mem=a.mem := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · interval_cases ph <;> exact legal_of_chain _ _ (by decide) (by simp [postRows,pcChain,execInstrBr,pc,address])
  · interval_cases ph <;> simp [postRows,walkRows,execInstrBr,pc,address]
  · simp [postRows,walkRows,execInstrBr,show signExtend12 1024#12=1024#64 by decide]
  · simp [postRows,walkRows,execInstrBr,show signExtend12 1536#12=1536#64 by decide]
  · simp [postRows,walkRows,execInstrBr,show signExtend12 1#12=1#64 by decide]
  · intro k h10 h12 h13; simp [postRows,walkRows,execInstrBr,Ne.symm h10,Ne.symm h12,Ne.symm h13]
  · simp [postRows,walkRows,execInstrBr]

theorem called_pc (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (y : BitVec 1600) :
    (called s ord y).pc=address (4111+272*(ord%4)) := by
  rw [show (called s ord y).pc=(walkRows s (headRows (ord%4))).pc+4 from reply_pc ..,(head_run s i ord left r).2.1]
  exact address_step _ _ (by omega)

theorem called_reg (s : MachineState) (ord : Nat) (y : BitVec 1600) (x : Reg) :
    (called s ord y).getReg x=(walkRows s (headRows (ord%4))).getReg x := writeBits_register ..

/-- The memory after the inverse call: the reply in the 25 block words, the rest as at entry. -/
theorem called_view (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (hj : ord ≤ 16777216)
    (y : BitVec 1600) (w : Nat) (fit : w<2^33) :
    memoryView (called s ord y) w=if h : blockW ord≤w ∧ w<blockW ord+25 then
      replyWords y ⟨w-blockW ord,by omega⟩ else memoryView s w := by
  have room := block_room ord hj
  change memoryView (writeBits (walkRows s (headRows (ord%4))) (wordAddress (blockW ord)) y) w=_
  rw [permutation_write_memory _ _ _ _ (by omega) fit,writeWindow]
  split
  · rfl
  · exact view_of_mem (head_run s i ord left r).2.2.1 w

/-- The registers after the head: the chain block's entry. -/
theorem headed_entry (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (hj : ord ≤ 16777216)
    (y : BitVec 1600) :
    ChainEntry (headed s ord y) i (ord%4) ∧
      (∀ k, k≠.x6 → k≠.x7 → k≠.x10 → k≠.x12 → k≠.x13 → k≠.x28 → k≠.x30 → k≠.x18 → k≠.x3 →
        (headed s ord y).getReg k=s.getReg k) ∧
      (headed s ord y).getReg .x12=1536 ∧ (headed s ord y).getReg .x13=1 ∧
      (headed s ord y).getReg .x18=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      (headed s ord y).mem=(called s ord y).mem := by
  unfold headed
  have hp : ord%4<4 := Nat.mod_lt _ (by decide)
  obtain ⟨_,_,_,_,t12,t13,t18,t6,_,_,t3,t30,tkeep⟩ := head_run s i ord left r
  have creg := called_reg s ord y
  obtain ⟨_,ppc,p10,p12,p13,pkeep,pmem⟩ := post_run (called s ord y) (ord%4) hp (called_pc s i ord left r y)
  set h := walkRows (called s ord y) (postRows (ord%4)) with hdef
  have k (x : Reg) (h10 : x≠.x10) (h12 : x≠.x12) (h13 : x≠.x13) : h.getReg x=(walkRows s (headRows (ord%4))).getReg x :=
    (pkeep x h10 h12 h13).trans (creg x)
  have kk (x : Reg) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide) (h10 : x≠.x10 := by decide)
      (h12 : x≠.x12 := by decide) (h13 : x≠.x13 := by decide) (h28 : x≠.x28 := by decide) (h30 : x≠.x30 := by decide)
      (h18 : x≠.x18 := by decide) (h3 : x≠.x3 := by decide) : h.getReg x=s.getReg x :=
    (k x h10 h12 h13).trans (tkeep x h6 h7 h10 h12 h13 h28 h30 h18 h3)
  have tab : TableAt h := by
    intro e he hh hh'
    have hi : i.val<16777216 := i.isLt
    have room := block_room ord hj
    have fit : tableWord e+hh<2^33 := by simp only [tableWord]; omega
    rw [view_of_mem pmem, called_view s i ord left r hj y _ fit, dif_neg (by simp only [tableWord]; omega)]
    exact r.table e he hh hh'
  refine ⟨⟨hp,ppc,p10,p12,kk .x5 ▸ r.selector,kk .x11 ▸ r.width,p13,?_,?_,?_,tab⟩,
    fun x h6 h7 h10 h12 h13 h28 h30 h18 h3 => kk x h6 h7 h10 h12 h13 h28 h30 h18 h3,p12,p13,?_,pmem⟩
  · exact (k _ (by decide) (by decide) (by decide)).trans t6
  · exact (k _ (by decide) (by decide) (by decide)).trans t3
  · exact (k _ (by decide) (by decide) (by decide)).trans t30
  · exact (k _ (by decide) (by decide) (by decide)).trans t18


/-! ### The chain -/

theorem tab_s_read (i : Index) : BitVec.ofNat 64 (tabS (i.val%4096))=readAt i := by
  unfold tabS tabOff readAt offAt rank
  congr 1

/-- The registers and memory the chain leaves for the record rows. -/
theorem chain_regs (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (hj : ord ≤ 16777216)
    (y : BitVec 1600) (t : MachineState) (hit : t ∈ support (chainTrace (headed s ord y) i (ord%4))) :
    t.pc=address (4156+272*(ord%4)) ∧ t.getReg .x28=readAt i ∧
      t.getReg .x6=BitVec.ofNat 64 i.val ∧ t.getReg .x12=1536 ∧ t.getReg .x13=1 ∧
      t.getReg .x18=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      (∀ k, k≠.x3 → k≠.x6 → k≠.x7 → k≠.x10 → k≠.x12 → k≠.x13 → k≠.x18 → k≠.x28 → k≠.x30 → k≠.x31 →
        t.getReg k=s.getReg k) ∧
      (∀ w, w<2^33 → w≠128 → (w<192 ∨ 217≤w) → memoryView t w=memoryView (called s ord y) w) := by
  obtain ⟨ent,hkeep,h12,h13,h18,hmem⟩ := headed_entry s i ord left r hj y
  obtain ⟨tpc,t28,_,tkeep,tview⟩ := chain_post _ i (ord%4) ent t hit
  have tk (x : Reg) (h3 : x≠.x3 := by decide) (h7 : x≠.x7 := by decide) (h10 : x≠.x10 := by decide)
      (h28 : x≠.x28 := by decide) (h30 : x≠.x30 := by decide) (h31 : x≠.x31 := by decide) :=
    tkeep x h3 h7 h10 h28 h30 h31
  refine ⟨tpc,t28.trans (tab_s_read i),(tk .x6).trans ent.idx,(tk .x12).trans h12,(tk .x13).trans h13,
    (tk .x18).trans h18,?_,?_⟩
  · intro k h3 h6 h7 h10 h12 h13 h18 h28 h30 h31
    rw [tkeep k h3 h7 h10 h28 h30 h31]; exact hkeep k h6 h7 h10 h12 h13 h28 h30 h18 h3
  · intro w hw n128 nsc
    rw [tview w hw n128 nsc, view_of_mem hmem]

end TwoPermutationPrototype.GroupedOpening.Layout2F
