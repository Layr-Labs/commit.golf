import CommitGolfCandidate.Layout2FusedRec

/-! Fused opener, one position: execution (`per_run`), the state after it (`trace_post`) and the fixed-oracle outcome. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2F
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolfCandidate.Layout2Phase (stride writerCarry)
open CommitGolfCandidate.Permutation.CounterSalt (coord)
open TwoPermutationPrototype.Sampling (saltWords)
open TwoPermutationPrototype.GroupedOpening.Layout2V2 (linkedSalts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

/-! ### One position -/

/-- The inverse query: the quartet's 200-byte reply in the trapdoor (the table entry's reply offset). -/
def inverseQuery (s : MachineState) (i : Index) : BitVec 1600 :=
  packBuffer (window (memoryView s) (replyWord (i.val/4)))

def perTrace (s : MachineState) (i : Index) (ord left : Nat) : OracleComp World MachineState := do
  let y ← World.query (.inr (.inr (.inr (inverseQuery s i))))
  let t ← chainTrace (headed s ord y) i (ord%4)
  return finish t ord left

def perSteps (i : Index) (ord left : Nat) := 17+(chainSteps i+recLen (ord%4) (decide (left=1)))
def perCycles (i : Index) (ord left : Nat) := 24+(chainCycles i+recLen (ord%4) (decide (left=1)))
def perCalls (i : Index) := 1+chainCalls i

theorem present_append {a b : List Row} (ha : presentRows a) (hb : presentRows b) : presentRows (a++b) :=
  fun p hp => (List.mem_append.mp hp).elim (ha p) (hb p)

private theorem charge_comm (e : Execution) (a b c d : Nat) :
    (e.charge a c).charge b d=e.charge (b+a) (d+c) := by
  cases e; simp [Execution.charge,Nat.add_assoc]

/-- The loop registers survive the head, the inverse call and the chain. -/
theorem chain_entry_regs (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (hj : ord ≤ 16777216)
    (y : BitVec 1600) (t : MachineState) (hit : t ∈ support (chainTrace (headed s ord y) i (ord%4))) :
    Regs t ord left ∧ t.getReg .x21=BitVec.ofNat 64 (destOf ord) ∧ t.getReg .x4=s.getReg .x4 := by
  obtain ⟨_,_,_,t12,t13,_,tkeep,_⟩ := chain_regs s i ord left r hj y t hit
  have k (x : Reg) (h3 : x≠.x3 := by decide) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide)
      (h10 : x≠.x10 := by decide) (h12 : x≠.x12 := by decide) (h13 : x≠.x13 := by decide) (h18 : x≠.x18 := by decide)
      (h28 : x≠.x28 := by decide) (h30 : x≠.x30 := by decide) (h31 : x≠.x31 := by decide) :=
    tkeep x h3 h6 h7 h10 h12 h13 h18 h28 h30 h31
  exact ⟨⟨t12,(k .x5).trans r.selector,(k .x11).trans r.width,t13,(k .x8).trans r.index,(k .x17).trans r.endReg,
    (k .x22).trans r.salt,(k .x26).trans r.base,(k .x9).trans r.heap,(k .x25).trans r.capHeap,(k .x19).trans r.leaves,
    (k .x20).trans r.start,(k .x23).trans r.mark,(k .x24).trans r.slots,(k .x27).trans r.capLeaves,
    (k .x2).trans r.sp,(k .x1).trans r.mask⟩,(k .x21).trans r.cursor,k .x4⟩

/-- One position: its head, the inverse call, the chained generator, the salt rows, the writer and the tail. -/
theorem per_run (s : MachineState) (i : Index) (ord left fuel : Nat) (l : 0<left) (bound : ord+left≤16777216)
    (r : Entry s i ord left) : execute openingImage (perSteps i ord left+fuel) s true =
      (do let t ← perTrace s i ord left; let z ← execute openingImage fuel t true
          return z.charge (perCycles i ord left) (perCalls i)) := by
  have hj : ord ≤ 16777216 := by omega
  have hp : ord%4<4 := Nat.mod_lt _ (by decide)
  obtain ⟨l1,apc,amem,a10,a12,a13,_,_,_,_,_,_,akeep⟩ := head_run s i ord left r
  have k (x : Reg) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide) (h10 : x≠.x10 := by decide)
      (h12 : x≠.x12 := by decide) (h13 : x≠.x13 := by decide) (h28 : x≠.x28 := by decide)
      (h30 : x≠.x30 := by decide) (h18 : x≠.x18 := by decide) (h3 : x≠.x3 := by decide) :=
    akeep x h6 h7 h10 h12 h13 h28 h30 h18 h3
  have room := block_room ord hj
  have hix : i.val<16777216 := i.isLt
  have src : replyWord (i.val/4)+25≤2^33 := by unfold replyWord blockWord; omega
  have dst : blockW ord+25≤2^33 := by omega
  have lens := row_lengths (ord%4)
  have rc := rec_cost (ord%4) hp (decide (left=1))
  rw [show perSteps i ord left+fuel=(headRows (ord%4)).length+(((postRows (ord%4)).length+(chainSteps i+
      ((recRows (ord%4) (decide (left=1))).length+fuel)))+1) by
      unfold perSteps; rw [lens.1, lens.2.2.1, rc.1]; omega,
    walk_rows_run s _ l1 (head_fetch _ hp) _ true,
    execute_inverse_call openingImage _ (walkRows s (headRows (ord%4))) true (replyWord (i.val/4)) (blockW ord)
      src dst a10 a12 ((k .x5).trans r.selector) ((k .x11).trans r.width) a13 (inverse_fetch _ _ hp apc)]
  have qeq : packBuffer (window (memoryView (walkRows s (headRows (ord%4)))) (replyWord (i.val/4)))=
      inverseQuery s i := by
    unfold inverseQuery; rw [show memoryView (walkRows s (headRows (ord%4)))=memoryView s from funext (view_of_mem amem)]
  rw [qeq]
  simp only [perTrace,bind_assoc,pure_bind]
  apply bind_congr; intro y
  have pl : legal (postRows (ord%4)) (called s ord y) :=
    (post_run _ _ hp (called_pc s i ord left r y)).1
  rw [show writeBits (walkRows s (headRows (ord%4))) (wordAddress (blockW ord)) y=called s ord y from rfl,
    walk_rows_run _ (postRows (ord%4)) pl (post_fetch _ hp) _ true,
    show walkRows (called s ord y) (postRows (ord%4))=headed s ord y from rfl,
    chain_run _ i (ord%4) (headed_entry s i ord left r hj y).1]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support; intro t hit
  obtain ⟨tpc,t28,t6,_,_,t18,_,_⟩ := chain_regs s i ord left r hj y t hit
  obtain ⟨tregs,t21,_⟩ := chain_entry_regs s i ord left r hj y t hit
  have fin := finish_facts t i ord left l bound tpc tregs t28 t21 t6 t18
  rw [walk_rows_run t _ fin.1 (rec_fetch _ hp _) fuel true]
  simp only [bind_assoc,pure_bind]
  apply bind_congr; intro e; apply congrArg Pure.pure
  rw [charge_comm, charge_comm, charge_comm, charge_comm, rc.2, lens.2.1, lens.2.2.2]
  unfold perCycles perCalls
  congr 1 <;> omega

/-- What one position leaves (for every oracle answer). -/
structure Post (s u : MachineState) (i : Index) (ord left : Nat) : Prop where
  regs : Regs u (ord+1) (left-1)
  pc : u.pc=finalPC ord left
  dest : u.getReg .x21=BitVec.ofNat 64 (destOf (ord+1))
  carry : u.getReg .x4=writerCarry (ord%4) (Layout2Phase.recordSource s (quadAddress i.val) i.val) (s.getReg .x4)
  mem : ∃ W : MachineState, u.mem=(W.setByte (markAt i) 1#8).mem ∧
    (∀ w<2^33, ¬Writes ord w → memoryView W w=memoryView s w) ∧
    (∀ b<stride (ord%4), Layout2Phase2.written (i.val%4) (b/8) →
      W.getByte (BitVec.ofNat 64 (destOf ord+b))=
        Layout2Phase2.writtenByte (ord%4) (Layout2Phase.recordSource s (quadAddress i.val) i.val) (s.getReg .x4) b)
  /-- The earlier record blocks are untouched. -/
  older : ∀ x, proofBase ≤ x → x<destOf ord → u.getByte (BitVec.ofNat 64 x)=s.getByte (BitVec.ofNat 64 x)

/-- A byte is read from its aligned word. -/
theorem byte_of_view {a b : MachineState} (x : Nat) (fx : x<2^36) (h : memoryView a (x/8)=memoryView b (x/8)) :
    a.getByte (BitVec.ofNat 64 x)=b.getByte (BitVec.ofNat 64 x) := by
  unfold MachineState.getByte
  rw [table_align_eq x (by omega)]
  have e : BitVec.ofNat 64 (x-x%8)=wordAddress (x/8) := by unfold wordAddress; congr 1; omega
  rw [e]
  change memoryView a (x/8)=memoryView b (x/8) at h
  exact congrArg (fun z => extractByte z (byteOffset (BitVec.ofNat 64 x))) h

/-- The record sources lie in the trapdoor region, which a position does not write. -/
theorem source_kept {a b : MachineState} (pos : Nat) (hp : pos<16777216)
    (frame : ∀ w<2^33, 536871428 ≤ w → 8*w<proofBase → memoryView a w=memoryView b w) (k : Nat) (hk : k<560) :
    Layout2Phase.recordSource a (quadAddress pos) pos k=Layout2Phase.recordSource b (quadAddress pos) pos k := by
  obtain ⟨lo,hi⟩ := source_inside pos k hp hk
  have tb : trapdoorBase=4294971424 := by decide
  have pb : proofBase=13824430176 := by decide
  unfold Layout2Phase.recordSource
  exact byte_of_view _ (by omega) (frame _ (by omega) (by omega) (by omega))

theorem written_src {a b : MachineState} (pos : Nat) (hp : pos<16777216)
    (frame : ∀ w<2^33, 536871428 ≤ w → 8*w<proofBase → memoryView a w=memoryView b w) (p : Nat) (c : Word) (j : Nat) :
    Layout2Phase2.writtenByte p (Layout2Phase.recordSource a (quadAddress pos) pos) c j=
      Layout2Phase2.writtenByte p (Layout2Phase.recordSource b (quadAddress pos) pos) c j :=
  written_byte_congr' (source_kept pos hp frame) p c j

theorem carry_src {a b : MachineState} (pos : Nat) (hp : pos<16777216)
    (frame : ∀ w<2^33, 536871428 ≤ w → 8*w<proofBase → memoryView a w=memoryView b w) (p : Nat) (c : Word) :
    writerCarry p (Layout2Phase.recordSource a (quadAddress pos) pos) c=
      writerCarry p (Layout2Phase.recordSource b (quadAddress pos) pos) c :=
  writer_carry_congr (source_kept pos hp frame) p c

theorem trace_post (s : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (bound : ord+left≤16777216)
    (r : Entry s i ord left) (u : MachineState) (hit : u ∈ support (perTrace s i ord left)) : Post s u i ord left := by
  have hj : ord ≤ 16777216 := by omega
  have room := block_room ord hj
  have pb : proofBase=13824430176 := rfl
  have ix : i.val<16777216 := i.isLt
  have sw := stride_words (ord%4)
  simp only [perTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨y,_,t,ht,rfl⟩ := hit
  obtain ⟨tpc,t28,t6,t12,t13,t18,tkeep,tview⟩ := chain_regs s i ord left r hj y t ht
  obtain ⟨tregs,t21,t4⟩ := chain_entry_regs s i ord left r hj y t ht
  obtain ⟨_,fpc,f21,f8,f4,fkeep,⟨W,wmem,wframe,wbytes,_⟩⟩ := finish_facts t i ord left l bound tpc tregs t28 t21 t6 t18
  -- the salt state, word by word, against the entry state
  have svView (w : Nat) (fit : w<2^33) (away : ¬Writes ord w) :
      memoryView (saltInstalled t ord i) w=memoryView s w := by
    have n128 : w≠128 := fun h => away (Or.inl h)
    have nsc : w<192 ∨ 217≤w := by by_contra h; exact away (Or.inr (Or.inl (by omega)))
    have nb : w<blockW ord ∨ blockW ord+stride (ord%4)/8≤w := by by_contra h; exact away (Or.inr (Or.inr (by omega)))
    rw [salt_view _ ord i hj w fit (by omega), tview w fit n128 nsc, called_view s i ord left r hj y w fit,
      dif_neg (by omega)]
  have srcFrame : ∀ w<2^33, 536871428 ≤ w → 8*w<proofBase →
      memoryView (saltInstalled t ord i) w=memoryView s w := by
    intro w fit lo hi
    exact svView w fit (by rintro (h|h|h) <;> unfold blockW at * <;> have := dest_bound ord <;> omega)
  have keepS (k : Reg) (sv : Saved k) : (finish t ord left).getReg k=s.getReg k := by
    obtain ⟨h3,h4,h6,h7,h8,h10,h12,h13,h18,h21,h28,h30,h31⟩ := sv
    rw [fkeep k h4 h6 h7 h8 h10 h21 h28 h31, tkeep k h3 h6 h7 h10 h12 h13 h18 h28 h30 h31]
  refine ⟨regs_of_saved r.toRegs keepS ?_ ?_ f8 l,fpc,f21,?_,⟨W,wmem,?_,?_⟩,?_⟩
  · rw [fkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact t12
  · rw [fkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact t13
  · rw [f4, t4, carry_src i.val ix srcFrame]
  · intro w fit away
    have nb : w<blockW ord ∨ blockW ord+stride (ord%4)/8≤w := by by_contra h; exact away (Or.inr (Or.inr (by omega)))
    have ta : (wordAddress w).toNat=8*w := by unfold wordAddress; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change W.getMem (wordAddress w)=_
    rw [wframe _ (by rw [ta]; have := block_mul ord; omega)]
    exact svView w fit away
  · intro b hb hw
    rw [wbytes b hb hw, written_src i.val ix srcFrame, t4]
  · intro x lo hi
    have fx : x<2^64 := by have := dest_bound ord; omega
    have g : 256+i.val/65536<512 := by omega
    have mk : markAt i=BitVec.ofNat 64 (Opening.markBase+(256+i.val/65536)) := rfl
    rw [byte_reads _ _ wmem, mk, byte_after_mark W _ _ g lo fx]
    have bm := block_mul ord
    have na : ¬Writes ord (x/8) := by rintro (h|h|h) <;> omega
    rw [byte_of_view _ (by omega) (show memoryView W (x/8)=memoryView s (x/8) from by
      have ta : (wordAddress (x/8)).toNat=8*(x/8) := by
        unfold wordAddress; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      change W.getMem (wordAddress (x/8))=_
      rw [wframe _ (by rw [ta]; omega)]
      exact svView (x/8) (by omega) na)]

/-! ### Fixed oracle -/

noncomputable def fixedInverse (o : Oracle) (s : MachineState) (i : Index) : BitVec 1600 :=
  o.permutation.symm (inverseQuery s i)
noncomputable def fixedHead (o : Oracle) (s : MachineState) (i : Index) (ord : Nat) : MachineState :=
  headed s ord (fixedInverse o s i)
noncomputable def fixedOne (o : Oracle) (s : MachineState) (i : Index) (ord left : Nat) : MachineState :=
  finish (chainState o (fixedHead o s i ord) i (ord%4)) ord left

theorem head_keys (s : MachineState) (i : Index) (ord left : Nat) (r : Entry s i ord left) (hj : ord ≤ 16777216)
    (y : BitVec 1600) (k : BitVec 192) (key : KeyWords s k) : KeyWords (headed s ord y) k := by
  have room := block_room ord hj
  have pb : proofBase=13824430176 := rfl
  intro j lo hi
  obtain ⟨_,_,_,_,_,hmem⟩ := headed_entry s i ord left r hj y
  rw [view_of_mem hmem, called_view s i ord left r hj y _ (by omega), dif_neg (by omega)]
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

/-- The fixed outcome's block before the writer: the linked salt in words 0..1, the inverse reply in words 2..24. -/
theorem fixed_salt_state (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left : Nat)
    (r : Entry s i ord left) (hj : ord ≤ 16777216) (key : KeyWords s k) :
    (∀ j : Fin 2, memoryView (saltInstalled (chainState o (fixedHead o s i ord) i (ord%4)) ord i) (blockW ord+j.val)=
      saltWords (linkedSalts o k i) j) ∧
    (∀ m (hm : m<25), 2≤m → memoryView (saltInstalled (chainState o (fixedHead o s i ord) i (ord%4)) ord i)
      (blockW ord+m)=replyWords (fixedInverse o s i) ⟨m,hm⟩) := by
  have room := block_room ord hj
  have pb : proofBase=13824430176 := rfl
  have ent := headed_entry s i ord left r hj (fixedInverse o s i)
  have hk : KeyWords (fixedHead o s i ord) k := head_keys s i ord left r hj (fixedInverse o s i) k key
  have mem : chainState o (fixedHead o s i ord) i (ord%4) ∈ support (chainTrace (fixedHead o s i ord) i (ord%4)) :=
    chain_state_support o k (fixedHead o s i ord) i _ ent.1 hk
  obtain ⟨_,_,_,_,_,_,_,uview⟩ := chain_regs s i ord left r hj (fixedInverse o s i) _ mem
  constructor
  · intro j
    have jj := j.isLt
    have sel : selectedWord i j<25 := by have:=salt_slot_bound (coord i).2;unfold selectedWord;omega
    rw [salt_words_at _ ord i hj j, salt_read, chain_reply o k (fixedHead o s i ord) i _ ent.1 hk ⟨selectedWord i j,sel⟩]
    exact congrFun (salt_slice_eq (chainReply o k i) (coord i).2) j
  · intro m hm two
    rw [salt_view _ ord i hj _ (by omega) (by omega), uview _ (by omega) (by omega) (Or.inr (by omega)),
      called_view s i ord left r hj _ _ (by omega), dif_pos (by omega)]
    congr 1; apply Fin.ext; simp

end TwoPermutationPrototype.GroupedOpening.Layout2F
