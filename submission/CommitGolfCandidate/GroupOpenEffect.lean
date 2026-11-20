import CommitGolfCandidate.GroupOpenLatch
import CommitGolfCandidate.GroupOpenVirtual
import CommitGolfCandidate.Machine
import CommitGolfCandidate.K3OpenReply

/-! K3-lite prefix, one position: the registers after it and its effect on the word view (rebuilt block
of a new quartet and the sibling-node pointer after it, generator scratch and counter, salt). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
open TwoPermutationPrototype.Sampling (saltWords)
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC

private theorem view_eq_of_mem {a b : MachineState} (h : a.mem=b.mem) (w : Nat) : memoryView a w=memoryView b w := by
  unfold memoryView MachineState.getMem; rw [h]

/-- Words the head of position `i` may write: its quartet's rebuilt block and the pointer word after it. -/
def HeadWrites (i : Index) (last : Nat) (w : Nat) : Prop :=
  i.val/4≠last ∧ ∃ m<26, w=rebuiltWord (i.val/4)+m

/-- The state after a new quartet's inverse call, before rows 773..776. -/
private def called (s : MachineState) (i : Index) (y : BitVec 1600) : MachineState :=
  writeBits (walkRows s (preRows (oddOf i))) (wordAddress (rebuiltWord (i.val/4))) y

private theorem called_facts (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (y : BitVec 1600) (fresh : i.val/4≠last) :
    let a1:=called s i y
    a1.pc=address 773 ∧ a1.getReg .x7=wordAddress (blockWord (i.val/4)) ∧
      a1.getReg .x30=wordAddress (nodeWordOf (i.val/4^^^1)) ∧
      (∀ w, w<2^33 → memoryView a1 w=if h : rebuiltWord (i.val/4)≤w ∧ w<rebuiltWord (i.val/4)+25 then
        replyWords y ⟨w-rebuiltWord (i.val/4),by omega⟩ else memoryView s w) := by
  have hi : i.val<16777216 := i.isLt
  obtain ⟨_,apc,amem,_,_,_,a30,_,_,_,a7,_⟩ := head_pre s i ord left last r fresh
  have reg1 (x : Reg) : (called s i y).getReg x=(walkRows s (preRows (oddOf i))).getReg x := writeBits_register ..
  refine ⟨?_,(reg1 _).trans a7,(reg1 _).trans a30,?_⟩
  · rw [show (called s i y).pc=(walkRows s (preRows (oddOf i))).pc+4 from reply_pc ..,apc]; rfl
  · intro w fit
    change memoryView (writeBits (walkRows s (preRows (oddOf i))) (wordAddress (rebuiltWord (i.val/4))) y) w=_
    rw [permutation_write_memory _ _ _ _ (by unfold rebuiltWord blockWord; omega) fit,writeWindow]
    split
    · rfl
    · exact view_eq_of_mem amem w

private theorem headed_fresh (s : MachineState) (i : Index) (last : Nat) (y : BitVec 1600) (fresh : i.val/4≠last) :
    headed s i last y=walkRows (called s i y) headPost := by simp [headed,fresh,called]

/-- Outside its writes and the scratch, the head keeps every word. -/
theorem head_outside (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (y : BitVec 1600) (w : Nat) (fit : w<2^33) (away : ¬HeadWrites i last w) (scratch : w<192 ∨ 217≤w) :
    memoryView (headed s i last y) w=memoryView s w := by
  have hi : i.val<16777216 := i.isLt
  by_cases same : i.val/4=last
  · have hd : headed s i last y=walkRows s headRows := by simp [headed,same]
    rw [hd]; exact view_eq_of_mem (head_skip s i ord left last r same).2.2.1 w
  · have notBlock : ∀ m<26, w≠rebuiltWord (i.val/4)+m := fun m hm e => away ⟨same,m,hm,e⟩
    obtain ⟨a1pc,a17,_,a1view⟩ := called_facts s i ord left last r y same
    obtain ⟨_,_,_,_,_,_,pview⟩ := head_post (called s i y) i a1pc a17
    rw [headed_fresh s i last y same, pview w fit]
    simp only [writeWord, if_neg (notBlock 25 (by omega))]
    rw [a1view w fit, dif_neg (fun h => notBlock (w-rebuiltWord (i.val/4)) (by omega) (by omega))]

/-- A new quartet's head stores the address of the sibling group's node in the pointer word. -/
theorem head_pointer (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (y : BitVec 1600) (fresh : i.val/4≠last) :
    memoryView (headed s i last y) (pointerWord (i.val/4))=wordAddress (nodeWordOf (i.val/4^^^1)) := by
  have hi : i.val<16777216 := i.isLt
  obtain ⟨a1pc,a17,a130,_⟩ := called_facts s i ord left last r y fresh
  obtain ⟨_,_,_,_,_,_,pview⟩ := head_post (called s i y) i a1pc a17
  rw [headed_fresh s i last y fresh, pview _ (by unfold pointerWord rebuiltWord blockWord; omega)]
  simp only [writeWord, ite_true]
  exact a130

/-- A new quartet's head leaves the inverse reply `y` in its rebuilt block. -/
theorem head_block (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (y : BitVec 1600) (fresh : i.val/4≠last) (m : Nat) (hm : m<25) :
    memoryView (headed s i last y) (rebuiltWord (i.val/4)+m)=replyWords y ⟨m,hm⟩ := by
  have hi : i.val<16777216 := i.isLt
  obtain ⟨a1pc,a17,_,a1view⟩ := called_facts s i ord left last r y fresh
  obtain ⟨_,_,_,_,_,_,pview⟩ := head_post (called s i y) i a1pc a17
  have fit : rebuiltWord (i.val/4)+m<2^33 := by unfold rebuiltWord blockWord; omega
  rw [headed_fresh s i last y fresh, pview _ fit]
  simp only [writeWord, pointerWord, show rebuiltWord (i.val/4)+m≠rebuiltWord (i.val/4)+25 by omega, ite_false]
  rw [a1view _ fit, dif_pos (by omega)]
  congr 1; apply Fin.ext; simp

/-- The head of position `i` keeps the generator key words. -/
theorem head_keys (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (y : BitVec 1600) (k : BitVec 192) (key : KeyWords s k) : KeyWords (headed s i last y) k := by
  intro j lo hi
  rw [head_outside s i ord left last r y (128+j) (by omega) (fun ⟨_,m,_,e⟩ => by
    have : i.val<16777216 := i.isLt
    unfold rebuiltWord blockWord at e; omega) (Or.inl (by omega))]
  exact key j lo hi

/-- Words a position may write: its head's, word 128 (counter), the scratch reply and its salt. -/
def Writes (i : Index) (last : Nat) (w : Nat) : Prop :=
  HeadWrites i last w ∨ w=128 ∨ (192≤w ∧ w<217) ∨ w=1140851204+2*i.val ∨ w=1140851204+2*i.val+1

def Saved (r : Reg) := r≠.x6 ∧ r≠.x7 ∧ r≠.x10 ∧ r≠.x13 ∧ r≠.x28 ∧ r≠.x30 ∧ r≠.x31 ∧ r≠.x14 ∧ r≠.x17 ∧ r≠.x4 ∧ r≠.x25

/-- The salt rows after the chain: registers of the next ordinal, the salt words installed. -/
theorem post_facts (u : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (hi : left≤16777216)
    (bound : ord+left≤16777216)
    (pc : u.pc=address 796) (regs : Registers u ord left) (idx : u.getReg .x6=BitVec.ofNat 64 i.val)
    (sub : u.getReg .x28=BitVec.ofNat 64 (rank i.val)) (one : u.getReg .x23=1) :
    Registers (finishOne u i left) (ord+1) (left-1) ∧ (finishOne u i left).pc=finalPC left ∧
      (finishOne u i left).mem=(installed u i).mem ∧
      (∀ k, k≠.x7 → k≠.x30 → k≠.x31 → k≠.x14 → k≠.x17 → k≠.x25 →
        (finishOne u i left).getReg k=u.getReg k) := by
  obtain ⟨ap,ar,ad⟩:=chosen u i pc idx sub one regs.output regs.salt
  let a:=choose u i
  let b:=copied a
  have keep (k : Reg) (h7 : k≠.x7) (h30 : k≠.x30) (h31 : k≠.x31) : b.getReg k=u.getReg k :=
    (copied_keeps a k h31).trans (choose_keeps u i k h7 h30)
  have hshift : b.getReg .x25=BitVec.ofNat 64 (8*(ord+left)) := by
    rw [show b.getReg .x25=u.getReg .x25 from keep .x25 (by decide) (by decide) (by decide), regs.shift]
    simp [show left≠0 by omega]
  have post:=next_ok b ord left (copied_pc a ap) l hi bound ((keep .x14 (by decide) (by decide) (by decide)).trans regs.index)
    ((keep .x17 (by decide) (by decide) (by decide)).trans regs.endReg) hshift
  have fk (k : Reg) (h7 : k≠.x7) (h30 : k≠.x30) (h31 : k≠.x31) (h14 : k≠.x14) (h17 : k≠.x17)
      (h25 : k≠.x25) :
      (finishOne u i left).getReg k=u.getReg k := (next_keeps b left k h14 h17 h25).trans (keep k h7 h30 h31)
  have f (k : Reg) (h7 : k≠.x7 := by decide) (h30 : k≠.x30 := by decide) (h31 : k≠.x31 := by decide)
      (h14 : k≠.x14 := by decide) (h17 : k≠.x17 := by decide) (h25 : k≠.x25 := by decide) := fk k h7 h30 h31 h14 h17 h25
  have hshift' : (advanced b left).getReg .x25=
      (if left-1=0 then u.getReg .x9 else BitVec.ofNat 64 (8*((ord+1)+(left-1)))) := by
    rw [post.2.2.2.2.1]
    by_cases z : left-1=0
    · rw [if_pos z,if_pos z,show b.getReg .x9=u.getReg .x9 from keep .x9 (by decide) (by decide) (by decide)]
    · rw [if_neg z,if_neg z]
  have hshift'' : (finishOne u i left).getReg .x25=
      (if left-1=0 then (finishOne u i left).getReg .x9 else BitVec.ofNat 64 (8*((ord+1)+(left-1)))) := by
    change (advanced b left).getReg .x25=_
    rw [hshift', f .x9]
  refine ⟨⟨(f .x10).trans regs.input,(f .x12).trans regs.output,(f .x5).trans regs.selector,(f .x11).trans regs.width,
    (f .x13).trans regs.primitive,post.2.2.1,post.2.2.2.1,hshift'',(f .x22).trans regs.salt,(f .x26).trans regs.base,
    (f .x29).trans regs.divReg⟩,post.2.1,?_,fk⟩
  exact post.2.2.2.2.2.trans ((copied_mem a i ar ad).trans (by
    change (installed (choose u i) i).mem=(installed u i).mem
    simp only [installed,MachineState.setMem,MachineState.getMem,chosen_memory u i]))

def selectedWord (i : Index) (j : Fin 2) := saltSlot (coord i).2+j.val

/-- The K1 reply offset of leaf `i` is the byte offset of its salt slot. -/
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

/-- The salt words of the position after the salt rows: the selected reply words. -/
theorem installs_salt (u : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (hi : left≤16777216)
    (bound : ord+left≤16777216) (pc : u.pc=address 796) (regs : Registers u ord left) (idx : u.getReg .x6=BitVec.ofNat 64 i.val)
    (sub : u.getReg .x28=BitVec.ofNat 64 (rank i.val)) (one : u.getReg .x23=1) (j : Fin 2) :
    (finishOne u i left).getMem (destAt i+BitVec.ofNat 64 (8*j.val))=memoryView u (192+selectedWord i j) := by
  have eq := (post_facts u i ord left l hi bound pc regs idx sub one).2.2.1
  rw [←salt_read u i j]
  change (finishOne u i left).mem _=_
  rw [eq];unfold installed
  fin_cases j <;> simp [MachineState.setMem,MachineState.getMem]

theorem salt_words (i : Index) : destAt i=wordAddress (1140851204+2*i.val) ∧
    destAt i+8=wordAddress (1140851204+2*i.val+1) := by
  have eq0 : destAt i=wordAddress (1140851204+2*i.val) := by unfold destAt wordAddress;congr 1 <;> omega
  exact ⟨eq0, by rw [eq0,wordAddress_add (1140851204+2*i.val) 1];rfl⟩

/-- Outside the salt words the salt rows keep the word view. -/
theorem post_outside (u : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (hi : left≤16777216)
    (bound : ord+left≤16777216) (pc : u.pc=address 796) (regs : Registers u ord left) (idx : u.getReg .x6=BitVec.ofNat 64 i.val)
    (sub : u.getReg .x28=BitVec.ofNat 64 (rank i.val)) (one : u.getReg .x23=1) (w : Nat) (fit : w<2^33)
    (apart : w≠1140851204+2*i.val ∧ w≠1140851204+2*i.val+1) :
    memoryView (finishOne u i left) w=memoryView u w := by
  have ix : i.val<16777216:=i.isLt
  have fin := (post_facts u i ord left l hi bound pc regs idx sub one).2.2.1
  obtain ⟨eq0,eq1⟩ := salt_words i
  have distinct (v : Nat) (hv : v<2^33) (ne : w≠v) : wordAddress w≠wordAddress v :=
    fun h => ne (wordAddress_injective_of_bound (by omega) (by omega) h)
  have n0 : wordAddress w≠destAt i := eq0 ▸ distinct _ (by omega) apart.1
  have n1 : wordAddress w≠destAt i+8 := eq1 ▸ distinct _ (by omega) apart.2
  rw [view_eq_of_mem fin]
  change (installed u i).getMem (wordAddress w)=_
  rw [installed,MachineState.getMem_setMem_ne n1,MachineState.getMem_setMem_ne n0]; rfl

/-- One outcome of a position, for its inverse reply `y` and chain outcome `u`. -/
theorem outcome_facts (s : MachineState) (i : Index) (ord left last : Nat) (l : 0<left) (hi : left≤16777216)
    (bound : ord+left≤16777216) (r : Input s i ord left last) (y : BitVec 1600) (u : MachineState)
    (hu : u ∈ support (chainTrace (headed s i last y) i)) :
    let t:=finishOne u i left
    Registers t (ord+1) (left-1) ∧ t.pc=finalPC left ∧ t.getReg .x4=BitVec.ofNat 64 (i.val/4) ∧
      (∀ k, Saved k → t.getReg k=s.getReg k) ∧
      (∀ w, w<2^33 → ¬Writes i last w → memoryView t w=memoryView s w) ∧
      (i.val/4≠last → memoryView t (pointerWord (i.val/4))=wordAddress (nodeWordOf (i.val/4^^^1))) := by
  have ex := head_exit s i ord left last r y
  obtain ⟨upc,u10,u28,ukeep,uview⟩ := chain_post _ i ex.entry u hu
  have uk (x : Reg) (h7 : x≠.x7 := by decide) (h10 : x≠.x10 := by decide) (h28 : x≠.x28 := by decide)
      (h30 : x≠.x30 := by decide) (h31 : x≠.x31 := by decide) := ukeep x h7 h10 h28 h30 h31
  have hk (x : Reg) (h4 : x≠.x4 := by decide) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide)
      (h10 : x≠.x10 := by decide) (h13 : x≠.x13 := by decide) (h28 : x≠.x28 := by decide)
      (h30 : x≠.x30 := by decide) (h31 : x≠.x31 := by decide) := ex.keep x h4 h6 h7 h10 h13 h28 h30 h31
  have uregs : Registers u ord left :=
    ⟨u10,(uk .x12).trans ex.regs.output,(uk .x5).trans ex.regs.selector,(uk .x11).trans ex.regs.width,
     (uk .x13).trans ex.regs.primitive,(uk .x14).trans ex.regs.index,(uk .x17).trans ex.regs.endReg,
     (by rw [uk .x25, ex.regs.shift, uk .x9]),
     (uk .x22).trans ex.regs.salt,(uk .x26).trans ex.regs.base,(uk .x29).trans ex.regs.divReg⟩
  have uone : u.getReg .x23=1 := (uk .x23).trans ((hk .x23).trans r.one)
  obtain ⟨pregs,ppc,_,pkeep⟩ := post_facts u i ord left l hi bound upc uregs ((uk .x6).trans ex.entry.idx) u28 uone
  refine ⟨pregs,ppc,?_,?_,?_,?_⟩
  · rw [pkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), uk .x4]; exact ex.quartet
  · intro k ⟨h6,h7,h10,h13,h28,h30,h31,h14,h17,h4,h25⟩
    rw [pkeep k h7 h30 h31 h14 h17 h25, ukeep k h7 h10 h28 h30 h31]; exact ex.keep k h4 h6 h7 h10 h13 h28 h30 h31
  · intro w fit away
    have nh : ¬HeadWrites i last w := fun h => away (Or.inl h)
    have n128 : w≠128 := fun h => away (Or.inr (Or.inl h))
    have nsc : w<192 ∨ 217≤w := by
      by_contra h; exact away (Or.inr (Or.inr (Or.inl (by omega))))
    have ns : w≠1140851204+2*i.val ∧ w≠1140851204+2*i.val+1 :=
      ⟨fun h => away (Or.inr (Or.inr (Or.inr (Or.inl h)))),fun h => away (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
    rw [post_outside u i ord left l hi bound upc uregs ((uk .x6).trans ex.entry.idx) u28 uone w fit ns,
      uview w fit n128 nsc]
    exact head_outside s i ord left last r y w fit nh nsc
  · intro fresh
    have ix : i.val<16777216 := i.isLt
    have fit : pointerWord (i.val/4)<2^33 := by unfold pointerWord rebuiltWord blockWord; omega
    rw [post_outside u i ord left l hi bound upc uregs ((uk .x6).trans ex.entry.idx) u28 uone _ fit
      ⟨by unfold pointerWord rebuiltWord blockWord; omega,by unfold pointerWord rebuiltWord blockWord; omega⟩,
      uview _ fit (by unfold pointerWord rebuiltWord blockWord; omega) (Or.inr (by unfold pointerWord rebuiltWord blockWord; omega))]
    exact head_pointer s i ord left last r y fresh

theorem trace_post (s : MachineState) (i : Index) (ord left last : Nat) (l : 0<left) (hi : left≤16777216)
    (bound : ord+left≤16777216) (r : Input s i ord left last) (t : MachineState) (hit : t ∈ support (perTrace s i left last)) :
    Registers t (ord+1) (left-1) ∧ t.pc=finalPC left ∧ t.getReg .x4=BitVec.ofNat 64 (i.val/4) ∧
      (∀ k, Saved k → t.getReg k=s.getReg k) ∧
      (∀ w, w<2^33 → ¬Writes i last w → memoryView t w=memoryView s w) ∧
      (i.val/4≠last → memoryView t (pointerWord (i.val/4))=wordAddress (nodeWordOf (i.val/4^^^1))) := by
  unfold perTrace at hit
  split at hit
  · simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨y,_,u,hu,rfl⟩ := hit
    exact outcome_facts s i ord left last l hi bound r y u hu
  · simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨u,hu,rfl⟩ := hit
    exact outcome_facts s i ord left last l hi bound r 0 u hu

/-! Fixed oracle: the outcome of a position and its contents. -/

noncomputable def fixedInverse (o : Oracle) (s : MachineState) (i : Index) : BitVec 1600 :=
  o.permutation.symm (inverseQuery s i)
noncomputable def fixedHead (o : Oracle) (s : MachineState) (i : Index) (last : Nat) : MachineState :=
  headed s i last (if inverts i last then fixedInverse o s i else 0)
noncomputable def fixedOne (o : Oracle) (s : MachineState) (i : Index) (left last : Nat) : MachineState :=
  finishOne (chainState o (fixedHead o s i last) i) i left

theorem trace_fixed (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (r : Input s i ord left last) (key : KeyWords s k) :
    o.run (perTrace s i left last)=pure (fixedOne o s i left last,perCalls i last) := by
  have helper (y : BitVec 1600) : o.run (do let t ← chainTrace (headed s i last y) i; return finishOne t i left)=
      pure (finishOne (chainState o (headed s i last y) i) i left,chainCalls i) := by
    rw [oracle_run_bind,chain_fixed o k _ i (head_exit s i ord left last r y).entry (head_keys s i ord left last r y k key)]
    simp [oracle_run_pure]
  unfold perTrace fixedOne fixedHead perCalls
  cases hinv : inverts i last
  · simp only [Bool.false_eq_true,ite_false]
    rw [helper 0]; simp
  · simp only [ite_true]
    rw [oracle_run_public_bind]
    simp only [Oracle.answer]
    erw [helper (o.permutation.symm (inverseQuery s i))]
    simp [fixedInverse]

theorem chain_state_support (o : Oracle) (k : BitVec 192) (h : MachineState) (i : Index) (e : ChainEntry h i)
    (key : KeyWords h k) : chainState o h i ∈ support (chainTrace h i) := by
  have h1 := chain_fixed o k h i e key
  unfold Oracle.run at h1
  exact writer_support (o.world.withAddCost Oracle.callCost) _ (chainState o h i,chainCalls i)
    (by rw [h1]; exact Set.mem_singleton _)

/-- The fixed outcome is an outcome of the position's trace. -/
theorem fixed_mem (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (r : Input s i ord left last) (key : KeyWords s k) :
    fixedOne o s i left last ∈ support (perTrace s i left last) := by
  unfold fixedOne fixedHead perTrace
  cases hinv : inverts i last
  · simp only [Bool.false_eq_true,ite_false,mem_support_bind_iff,support_pure,Set.mem_singleton_iff]
    exact ⟨_,chain_state_support o k _ i (head_exit s i ord left last r 0).entry
      (head_keys s i ord left last r 0 k key),rfl⟩
  · simp only [ite_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff]
    refine ⟨fixedInverse o s i,mem_support_query _ _,_,chain_state_support o k _ i (head_exit s i ord left last r _).entry
      (head_keys s i ord left last r _ k key),rfl⟩

/-- The chain outcome of the fixed head, with the facts the salt rows need. -/
private theorem fixed_chain (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (r : Input s i ord left last) (key : KeyWords s k) :
    let h:=fixedHead o s i last
    let u:=chainState o h i
    u.pc=address 796 ∧ Registers u ord left ∧ u.getReg .x6=BitVec.ofNat 64 i.val ∧
      u.getReg .x28=BitVec.ofNat 64 (rank i.val) ∧ u.getReg .x23=1 ∧
      (∀ w, w<2^33 → w≠128 → (w<192 ∨ 217≤w) → memoryView u w=memoryView h w) ∧
      (∀ j : Fin 25, memoryView u (192+j.val)=replyWords (chainReply o k i) j) := by
  have ex := head_exit s i ord left last r (if inverts i last then fixedInverse o s i else 0)
  have hk := head_keys s i ord left last r (if inverts i last then fixedInverse o s i else 0) k key
  obtain ⟨upc,u10,u28,ukeep,uview⟩ := chain_post _ i ex.entry _ (chain_state_support o k _ i ex.entry hk)
  have uk (x : Reg) (h7 : x≠.x7 := by decide) (h10 : x≠.x10 := by decide) (h28 : x≠.x28 := by decide)
      (h30 : x≠.x30 := by decide) (h31 : x≠.x31 := by decide) := ukeep x h7 h10 h28 h30 h31
  refine ⟨upc,⟨u10,(uk .x12).trans ex.regs.output,(uk .x5).trans ex.regs.selector,(uk .x11).trans ex.regs.width,
     (uk .x13).trans ex.regs.primitive,(uk .x14).trans ex.regs.index,(uk .x17).trans ex.regs.endReg,
     (by rw [show fixedHead o s i last=headed s i last (if inverts i last then fixedInverse o s i else 0) from rfl, uk .x25, ex.regs.shift, uk .x9]),
     (uk .x22).trans ex.regs.salt,(uk .x26).trans ex.regs.base,(uk .x29).trans ex.regs.divReg⟩,
    (uk .x6).trans ex.entry.idx,u28,(uk .x23).trans ((ex.keep _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans r.one),uview,
    chain_reply o k _ i ex.entry hk⟩

/-- The fixed outcome's salt words: the linked schedule's salt of `i`. -/
theorem fixed_salt (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (l : 0<left) (hi : left≤16777216) (bound : ord+left≤16777216) (r : Input s i ord left last) (key : KeyWords s k) (j : Fin 2) :
    (fixedOne o s i left last).getMem (destAt i+BitVec.ofNat 64 (8*j.val))=
      saltWords (Permutation.LinkedSalt.salts (Permutation.LinkedSalt.schedule Permutation.LinkedSalt.period)
        o.permutation k i) j := by
  obtain ⟨upc,uregs,u6,u28,u23,_,ureply⟩ := fixed_chain o k s i ord left last r key
  have jj := j.isLt
  have sel : selectedWord i j<25 := by have:=salt_slot_bound (coord i).2;unfold selectedWord;omega
  unfold fixedOne
  rw [installs_salt _ i ord left l hi bound upc uregs u6 u28 u23 j, ureply ⟨selectedWord i j,sel⟩]
  exact congrFun (salt_slice_eq (chainReply o k i) (coord i).2) j

/-- The fixed outcome keeps the head's words outside word 128, the scratch and the salt. -/
theorem fixed_outside (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (l : 0<left) (hi : left≤16777216) (bound : ord+left≤16777216) (r : Input s i ord left last) (key : KeyWords s k) (w : Nat) (fit : w<2^33)
    (n128 : w≠128) (nsc : w<192 ∨ 217≤w) (ns : w≠1140851204+2*i.val ∧ w≠1140851204+2*i.val+1) :
    memoryView (fixedOne o s i left last) w=memoryView (fixedHead o s i last) w := by
  obtain ⟨upc,uregs,u6,u28,u23,uview,_⟩ := fixed_chain o k s i ord left last r key
  unfold fixedOne
  rw [post_outside _ i ord left l hi bound upc uregs u6 u28 u23 w fit ns, uview w fit n128 nsc]

theorem inverse_query_eq (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (fresh : i.val/4≠last) :
    inverseQuery s i=packBuffer (window (memoryView s) (replyWord (i.val/4))) := by
  have m := (head_pre s i ord left last r fresh).2.2.1
  unfold inverseQuery
  congr 2; funext j
  exact view_eq_of_mem m _

/-- A new quartet: the fixed outcome holds the inverse of its reply in its rebuilt block. -/
theorem fixed_block (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (l : 0<left) (hi : left≤16777216) (bound : ord+left≤16777216) (r : Input s i ord left last) (key : KeyWords s k)
    (fresh : i.val/4≠last) (m : Nat) (hm : m<25) :
    memoryView (fixedOne o s i left last) (rebuiltWord (i.val/4)+m)=
      replyWords (o.permutation.symm (packBuffer (window (memoryView s) (replyWord (i.val/4))))) ⟨m,hm⟩ := by
  have ix : i.val<16777216 := i.isLt
  rw [fixed_outside o k s i ord left last l hi bound r key _ (by unfold rebuiltWord blockWord; omega)
    (by unfold rebuiltWord blockWord; omega) (Or.inr (by unfold rebuiltWord blockWord; omega))
    ⟨by unfold rebuiltWord blockWord; omega,by unfold rebuiltWord blockWord; omega⟩]
  have inv : inverts i last=true := by simp [inverts,fresh]
  unfold fixedHead; rw [inv, if_pos rfl, head_block s i ord left last r _ fresh m hm, fixedInverse,
    inverse_query_eq s i ord left last r fresh]

/-- A new quartet: the fixed outcome holds the sibling group's node address in its pointer word. -/
theorem fixed_pointer (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (l : 0<left) (hi : left≤16777216) (bound : ord+left≤16777216) (r : Input s i ord left last) (key : KeyWords s k)
    (fresh : i.val/4≠last) :
    memoryView (fixedOne o s i left last) (pointerWord (i.val/4))=wordAddress (nodeWordOf (i.val/4^^^1)) := by
  have ix : i.val<16777216 := i.isLt
  rw [fixed_outside o k s i ord left last l hi bound r key _ (by unfold pointerWord rebuiltWord blockWord; omega)
    (by unfold pointerWord rebuiltWord blockWord; omega) (Or.inr (by unfold pointerWord rebuiltWord blockWord; omega))
    ⟨by unfold pointerWord rebuiltWord blockWord; omega,by unfold pointerWord rebuiltWord blockWord; omega⟩]
  unfold fixedHead; exact head_pointer s i ord left last r _ fresh

end TwoPermutationPrototype.GroupedOpening
