import CommitGolfCandidate.GroupOpenLatch
import CommitGolfCandidate.GroupOpenVirtual
import CommitGolfCandidate.Machine
import CommitGolfCandidate.K3GRBridge

/-! K3-lite prefix, one position: the registers after it and its effect on the word view (level-22
sibling, d3 of a new even quartet, generator scratch and counter, salt). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
open TwoPermutationPrototype.Sampling (saltWords)
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC

theorem sib_pairs_diag : ∀ p ∈ sibPairs, p.1=p.2 ∧ p.2<4 := by decide
theorem d3_pairs_diag : ∀ p ∈ d3Pairs, p.1=p.2 ∧ 21≤p.2 ∧ p.2<25 := by decide
theorem sib_member (m : Nat) (hm : m<4) : (m,m) ∈ sibPairs := by interval_cases m <;> decide
theorem d3_member (m : Nat) (hm : m<4) : (21+m,21+m) ∈ d3Pairs := by interval_cases m <;> decide

private theorem view_eq_of_mem {a b : MachineState} (h : a.mem=b.mem) (w : Nat) : memoryView a w=memoryView b w := by
  unfold memoryView MachineState.getMem; rw [h]

/-- Words the head of position `i` may write: the level-22 sibling slot and, for an even quartet, its d3. -/
def HeadWrites (i : Index) (last : Nat) (w : Nat) : Prop :=
  i.val/4≠last ∧ ((∃ m<4, w=heapWord (4194304+(i.val/4^^^1))+m) ∨ (i.val/4%2=0 ∧ ∃ m<4, w=replyEWord (i.val/4)+m))

private theorem sib_away (i : Index) (w : Nat) (h : ∀ m<4, w≠heapWord (4194304+(i.val/4^^^1))+m) :
    ∀ p ∈ sibPairs, w≠heapWord (4194304+(i.val/4^^^1))+p.2 := by
  intro p hp
  have r : p.2<4 := (sib_pairs_diag p hp).2
  exact h p.2 r

private theorem d3_away (q w : Nat) (h : ∀ m<4, w≠replyEWord q+m) : ∀ p ∈ d3Pairs, w≠blockWord q+p.2 := by
  intro p hp
  have r : 21≤p.2 ∧ p.2<25 := (d3_pairs_diag p hp).2
  have := h (p.2-21) (by omega)
  unfold replyEWord at this; rw [show blockWord q+21+(p.2-21)=blockWord q+p.2 by omega] at this
  exact this

/-- Outside its writes and the scratch, the head keeps every word. -/
theorem head_outside (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (y : BitVec 1600) (w : Nat) (fit : w<2^33) (away : ¬HeadWrites i last w) (scratch : w<192 ∨ 217≤w) :
    memoryView (headed s i last y) w=memoryView s w := by
  have hi : i.val<16777216 := i.isLt
  by_cases same : i.val/4=last
  · have hd : headed s i last y=walkRows s headRows := by simp [headed,same]
    rw [hd]; exact view_eq_of_mem (head_skip s i ord left last r same).2.2.1 w
  · have notSib : ∀ m<4, w≠heapWord (4194304+(i.val/4^^^1))+m :=
      fun m hm e => away ⟨same,Or.inl ⟨m,hm,e⟩⟩
    by_cases odd : i.val/4%2=1
    · have hd : headed s i last y=walkRows s oddPath := by simp [headed,same,odd]
      rw [hd, (head_odd s i ord left last r same odd).2.2.2.2.2 w fit]
      exact pair_view_outside _ _ _ _ _ _ (sib_away i w notSib)
    · have even : i.val/4%2=0 := by omega
      have notD3 : ∀ m<4, w≠replyEWord (i.val/4)+m := fun m hm e => away ⟨same,Or.inr ⟨even,m,hm,e⟩⟩
      obtain ⟨_,apc,amem,_,_,_,a28,_,a7,akeep⟩ := head_even_pre s i ord left last r same even
      let a1:=writeBits (walkRows s evenPre) (wordAddress 192) y
      have reg1 (x : Reg) : a1.getReg x=(walkRows s evenPre).getReg x := writeBits_register ..
      have a1pc : a1.pc=address 752 := by rw [show a1.pc=(walkRows s evenPre).pc+4 from reply_pc ..,apc]; rfl
      have k (x : Reg) (h4 : x≠.x4 := by decide) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide)
          (h10 : x≠.x10 := by decide) (h13 : x≠.x13 := by decide) (h28 : x≠.x28 := by decide)
          (h30 : x≠.x30 := by decide) : a1.getReg x=s.getReg x := (reg1 x).trans (akeep x h4 h6 h7 h10 h13 h28 h30)
      obtain ⟨_,_,_,_,_,pview⟩ := head_even_post a1 i a1pc even ((k .x12).trans r.output)
        ((reg1 _).trans a28) ((reg1 _).trans a7) ((k .x19).trans r.leaves) ((k .x9).trans r.heap)
      have hd : headed s i last y=walkRows a1 evenPost := by simp [headed,same,odd,a1]
      rw [hd, pview w fit, pair_view_outside _ _ _ _ _ _ (sib_away i w notSib),
        pair_view_outside _ _ _ _ _ _ (d3_away _ w notD3)]
      change memoryView (writeBits (walkRows s evenPre) (wordAddress 192) y) w=_
      rw [permutation_write_memory _ _ _ _ (by decide) fit,writeWindow,dif_neg (by omega)]
      exact view_eq_of_mem amem w

/-- A new quartet's head copies the sibling group's node into its level-22 heap slot. -/
theorem head_sibling (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (y : BitVec 1600) (fresh : i.val/4≠last) (m : Nat) (hm : m<4) :
    memoryView (headed s i last y) (heapWord (4194304+(i.val/4^^^1))+m)=memoryView s (nodeWordOf (i.val/4^^^1)+m) := by
  have hi : i.val<16777216 := i.isLt
  have gx := xor_one_lt (i.val/4) 22 (by omega) (by decide)
  have member : (m,m) ∈ sibPairs := sib_member m hm
  have uniq : ∀ p ∈ sibPairs, heapWord (4194304+(i.val/4^^^1))+p.2=heapWord (4194304+(i.val/4^^^1))+m → p.1=m := by
    intro p hp e
    have r : p.1=p.2 := (sib_pairs_diag p hp).1
    omega
  have fit : heapWord (4194304+(i.val/4^^^1))+m<2^33 := by unfold heapWord; omega
  by_cases odd : i.val/4%2=1
  · have hd : headed s i last y=walkRows s oddPath := by simp [headed,fresh,odd]
    rw [hd, (head_odd s i ord left last r fresh odd).2.2.2.2.2 _ fit]
    exact pair_view_inside sibPairs _ _ _ _ m m member uniq
  · have even : i.val/4%2=0 := by omega
    obtain ⟨_,apc,amem,_,_,_,a28,_,a7,akeep⟩ := head_even_pre s i ord left last r fresh even
    let a1:=writeBits (walkRows s evenPre) (wordAddress 192) y
    have reg1 (x : Reg) : a1.getReg x=(walkRows s evenPre).getReg x := writeBits_register ..
    have a1pc : a1.pc=address 752 := by rw [show a1.pc=(walkRows s evenPre).pc+4 from reply_pc ..,apc]; rfl
    have k (x : Reg) (h4 : x≠.x4 := by decide) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide)
        (h10 : x≠.x10 := by decide) (h13 : x≠.x13 := by decide) (h28 : x≠.x28 := by decide)
        (h30 : x≠.x30 := by decide) : a1.getReg x=s.getReg x := (reg1 x).trans (akeep x h4 h6 h7 h10 h13 h28 h30)
    obtain ⟨_,_,_,_,_,pview⟩ := head_even_post a1 i a1pc even ((k .x12).trans r.output)
      ((reg1 _).trans a28) ((reg1 _).trans a7) ((k .x19).trans r.leaves) ((k .x9).trans r.heap)
    have hd : headed s i last y=walkRows a1 evenPost := by simp [headed,fresh,odd,a1]
    rw [hd, pview _ fit, pair_view_inside sibPairs _ _ _ _ m m member uniq]
    have nfit : nodeWordOf (i.val/4^^^1)+m<2^33 := by
      obtain ⟨d,_⟩ := xor_one (i.val/4); unfold nodeWordOf blockWord; rw [d]; omega
    change memoryView (writeBits (walkRows s evenPre) (wordAddress 192) y) _=_
    rw [permutation_write_memory _ _ _ _ (by decide) nfit,writeWindow,dif_neg (by
      obtain ⟨d,_⟩ := xor_one (i.val/4); unfold nodeWordOf blockWord; rw [d]; omega)]
    exact view_eq_of_mem amem _

/-- A new even quartet's head writes d3 (inverse reply words 21..24) back over reply_E. -/
theorem head_d3 (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (y : BitVec 1600) (fresh : i.val/4≠last) (even : i.val/4%2=0) (m : Nat) (hm : m<4) :
    memoryView (headed s i last y) (replyEWord (i.val/4)+m)=replyWords y ⟨21+m,by omega⟩ := by
  have hi : i.val<16777216 := i.isLt
  have gx := xor_one_lt (i.val/4) 22 (by omega) (by decide)
  obtain ⟨_,apc,amem,_,_,_,a28,_,a7,akeep⟩ := head_even_pre s i ord left last r fresh even
  let a1:=writeBits (walkRows s evenPre) (wordAddress 192) y
  have reg1 (x : Reg) : a1.getReg x=(walkRows s evenPre).getReg x := writeBits_register ..
  have a1pc : a1.pc=address 752 := by rw [show a1.pc=(walkRows s evenPre).pc+4 from reply_pc ..,apc]; rfl
  have k (x : Reg) (h4 : x≠.x4 := by decide) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide)
      (h10 : x≠.x10 := by decide) (h13 : x≠.x13 := by decide) (h28 : x≠.x28 := by decide)
      (h30 : x≠.x30 := by decide) : a1.getReg x=s.getReg x := (reg1 x).trans (akeep x h4 h6 h7 h10 h13 h28 h30)
  obtain ⟨_,_,_,_,_,pview⟩ := head_even_post a1 i a1pc even ((k .x12).trans r.output)
    ((reg1 _).trans a28) ((reg1 _).trans a7) ((k .x19).trans r.leaves) ((k .x9).trans r.heap)
  have odd : ¬i.val/4%2=1 := by omega
  have hd : headed s i last y=walkRows a1 evenPost := by simp [headed,fresh,odd,a1]
  have fit : replyEWord (i.val/4)+m<2^33 := by unfold replyEWord blockWord; omega
  rw [hd, pview _ fit]
  rw [pair_view_outside _ _ _ _ _ _ (fun p hp => by
    have r : p.2<4 := (sib_pairs_diag p hp).2
    unfold replyEWord blockWord heapWord; omega)]
  have member : (21+m,21+m) ∈ d3Pairs := d3_member m hm
  rw [show replyEWord (i.val/4)+m=blockWord (i.val/4)+(21+m) by unfold replyEWord; omega,
    pair_view_inside d3Pairs _ _ _ _ _ _ member (fun p hp e => by
      have r : p.1=p.2 := (d3_pairs_diag p hp).1
      omega)]
  change memoryView (writeBits (walkRows s evenPre) (wordAddress 192) y) _=_
  rw [permutation_write_memory _ _ _ _ (by decide) (by omega),writeWindow,dif_pos (by omega)]
  congr 1; apply Fin.ext; simp

/-- The head of position `i` keeps the generator key words. -/
theorem head_keys (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (y : BitVec 1600) (k : BitVec 192) (key : KeyWords s k) : KeyWords (headed s i last y) k := by
  intro j lo hi
  rw [head_outside s i ord left last r y (128+j) (by omega) (fun ⟨_,h⟩ => by
    have : i.val<16777216 := i.isLt
    rcases h with ⟨m,_,e⟩|⟨_,m,_,e⟩
    · unfold heapWord at e; omega
    · unfold replyEWord blockWord at e; omega) (Or.inl (by omega))]
  exact key j lo hi

/-- Words a position may write: its head's, word 128 (counter), the scratch reply and its salt. -/
def Writes (i : Index) (last : Nat) (w : Nat) : Prop :=
  HeadWrites i last w ∨ w=128 ∨ (192≤w ∧ w<217) ∨ w=1140851204+2*i.val ∨ w=1140851204+2*i.val+1

def Saved (r : Reg) := r≠.x6 ∧ r≠.x7 ∧ r≠.x10 ∧ r≠.x13 ∧ r≠.x28 ∧ r≠.x30 ∧ r≠.x31 ∧ r≠.x14 ∧ r≠.x17 ∧ r≠.x4

/-- The salt rows after the chain: registers of the next ordinal, the salt words installed. -/
theorem post_facts (u : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (hi : left≤16777216)
    (pc : u.pc=address 796) (regs : Registers u ord left) (idx : u.getReg .x6=BitVec.ofNat 64 i.val)
    (sub : u.getReg .x28=BitVec.ofNat 64 (rank i.val)) (one : u.getReg .x23=1) :
    Registers (finishOne u i left) (ord+1) (left-1) ∧ (finishOne u i left).pc=finalPC left ∧
      (finishOne u i left).mem=(installed u i).mem ∧
      (∀ k, k≠.x7 → k≠.x30 → k≠.x31 → k≠.x14 → k≠.x17 → (finishOne u i left).getReg k=u.getReg k) := by
  obtain ⟨ap,ar,ad⟩:=chosen u i pc idx sub one regs.output regs.salt
  let a:=choose u i
  let b:=copied a
  have keep (k : Reg) (h7 : k≠.x7) (h30 : k≠.x30) (h31 : k≠.x31) : b.getReg k=u.getReg k :=
    (copied_keeps a k h31).trans (choose_keeps u i k h7 h30)
  have post:=next_ok b ord left (copied_pc a ap) l hi ((keep .x14 (by decide) (by decide) (by decide)).trans regs.index)
    ((keep .x17 (by decide) (by decide) (by decide)).trans regs.leftReg)
  have fk (k : Reg) (h7 : k≠.x7) (h30 : k≠.x30) (h31 : k≠.x31) (h14 : k≠.x14) (h17 : k≠.x17) :
      (finishOne u i left).getReg k=u.getReg k := (next_keeps b left k h14 h17).trans (keep k h7 h30 h31)
  have f (k : Reg) (h7 : k≠.x7 := by decide) (h30 : k≠.x30 := by decide) (h31 : k≠.x31 := by decide)
      (h14 : k≠.x14 := by decide) (h17 : k≠.x17 := by decide) := fk k h7 h30 h31 h14 h17
  refine ⟨⟨(f .x10).trans regs.input,(f .x12).trans regs.output,(f .x5).trans regs.selector,(f .x11).trans regs.width,
    (f .x13).trans regs.primitive,post.2.2.1,post.2.2.2.1,(f .x22).trans regs.salt,(f .x26).trans regs.base,
    (f .x29).trans regs.divReg⟩,post.2.1,?_,fk⟩
  exact post.2.2.2.2.trans ((copied_mem a i ar ad).trans (by
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
    (pc : u.pc=address 796) (regs : Registers u ord left) (idx : u.getReg .x6=BitVec.ofNat 64 i.val)
    (sub : u.getReg .x28=BitVec.ofNat 64 (rank i.val)) (one : u.getReg .x23=1) (j : Fin 2) :
    (finishOne u i left).getMem (destAt i+BitVec.ofNat 64 (8*j.val))=memoryView u (192+selectedWord i j) := by
  have eq := (post_facts u i ord left l hi pc regs idx sub one).2.2.1
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
    (pc : u.pc=address 796) (regs : Registers u ord left) (idx : u.getReg .x6=BitVec.ofNat 64 i.val)
    (sub : u.getReg .x28=BitVec.ofNat 64 (rank i.val)) (one : u.getReg .x23=1) (w : Nat) (fit : w<2^33)
    (apart : w≠1140851204+2*i.val ∧ w≠1140851204+2*i.val+1) :
    memoryView (finishOne u i left) w=memoryView u w := by
  have ix : i.val<16777216:=i.isLt
  have fin := (post_facts u i ord left l hi pc regs idx sub one).2.2.1
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
    (r : Input s i ord left last) (y : BitVec 1600) (u : MachineState)
    (hu : u ∈ support (chainTrace (headed s i last y) i)) :
    let t:=finishOne u i left
    Registers t (ord+1) (left-1) ∧ t.pc=finalPC left ∧ t.getReg .x4=BitVec.ofNat 64 (i.val/4) ∧
      (∀ k, Saved k → t.getReg k=s.getReg k) ∧
      (∀ w, w<2^33 → ¬Writes i last w → memoryView t w=memoryView s w) := by
  have ex := head_exit s i ord left last r y
  obtain ⟨upc,u10,u28,ukeep,uview⟩ := chain_post _ i ex.entry u hu
  have uk (x : Reg) (h7 : x≠.x7 := by decide) (h10 : x≠.x10 := by decide) (h28 : x≠.x28 := by decide)
      (h30 : x≠.x30 := by decide) (h31 : x≠.x31 := by decide) := ukeep x h7 h10 h28 h30 h31
  have hk (x : Reg) (h4 : x≠.x4 := by decide) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide)
      (h10 : x≠.x10 := by decide) (h13 : x≠.x13 := by decide) (h28 : x≠.x28 := by decide)
      (h30 : x≠.x30 := by decide) (h31 : x≠.x31 := by decide) := ex.keep x h4 h6 h7 h10 h13 h28 h30 h31
  have uregs : Registers u ord left :=
    ⟨u10,(uk .x12).trans ex.regs.output,(uk .x5).trans ex.regs.selector,(uk .x11).trans ex.regs.width,
     (uk .x13).trans ex.regs.primitive,(uk .x14).trans ex.regs.index,(uk .x17).trans ex.regs.leftReg,
     (uk .x22).trans ex.regs.salt,(uk .x26).trans ex.regs.base,(uk .x29).trans ex.regs.divReg⟩
  have uone : u.getReg .x23=1 := (uk .x23).trans ((hk .x23).trans r.one)
  obtain ⟨pregs,ppc,_,pkeep⟩ := post_facts u i ord left l hi upc uregs ((uk .x6).trans ex.entry.idx) u28 uone
  refine ⟨pregs,ppc,?_,?_,?_⟩
  · rw [pkeep _ (by decide) (by decide) (by decide) (by decide) (by decide), uk .x4]; exact ex.quartet
  · intro k ⟨h6,h7,h10,h13,h28,h30,h31,h14,h17,h4⟩
    rw [pkeep k h7 h30 h31 h14 h17, ukeep k h7 h10 h28 h30 h31]; exact ex.keep k h4 h6 h7 h10 h13 h28 h30 h31
  · intro w fit away
    have nh : ¬HeadWrites i last w := fun h => away (Or.inl h)
    have n128 : w≠128 := fun h => away (Or.inr (Or.inl h))
    have nsc : w<192 ∨ 217≤w := by
      by_contra h; exact away (Or.inr (Or.inr (Or.inl (by omega))))
    have ns : w≠1140851204+2*i.val ∧ w≠1140851204+2*i.val+1 :=
      ⟨fun h => away (Or.inr (Or.inr (Or.inr (Or.inl h)))),fun h => away (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
    rw [post_outside u i ord left l hi upc uregs ((uk .x6).trans ex.entry.idx) u28 uone w fit ns,
      uview w fit n128 nsc]
    exact head_outside s i ord left last r y w fit nh nsc

theorem trace_post (s : MachineState) (i : Index) (ord left last : Nat) (l : 0<left) (hi : left≤16777216)
    (r : Input s i ord left last) (t : MachineState) (hit : t ∈ support (perTrace s i left last)) :
    Registers t (ord+1) (left-1) ∧ t.pc=finalPC left ∧ t.getReg .x4=BitVec.ofNat 64 (i.val/4) ∧
      (∀ k, Saved k → t.getReg k=s.getReg k) ∧
      (∀ w, w<2^33 → ¬Writes i last w → memoryView t w=memoryView s w) := by
  unfold perTrace at hit
  split at hit
  · simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨y,_,u,hu,rfl⟩ := hit
    exact outcome_facts s i ord left last l hi r y u hu
  · simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨u,hu,rfl⟩ := hit
    exact outcome_facts s i ord left last l hi r 0 u hu

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
     (uk .x13).trans ex.regs.primitive,(uk .x14).trans ex.regs.index,(uk .x17).trans ex.regs.leftReg,
     (uk .x22).trans ex.regs.salt,(uk .x26).trans ex.regs.base,(uk .x29).trans ex.regs.divReg⟩,
    (uk .x6).trans ex.entry.idx,u28,(uk .x23).trans ((ex.keep _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans r.one),uview,
    chain_reply o k _ i ex.entry hk⟩

/-- The fixed outcome's salt words: the linked schedule's salt of `i`. -/
theorem fixed_salt (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (l : 0<left) (hi : left≤16777216) (r : Input s i ord left last) (key : KeyWords s k) (j : Fin 2) :
    (fixedOne o s i left last).getMem (destAt i+BitVec.ofNat 64 (8*j.val))=
      saltWords (Permutation.LinkedSalt.salts (Permutation.LinkedSalt.schedule Permutation.LinkedSalt.period)
        o.permutation k i) j := by
  obtain ⟨upc,uregs,u6,u28,u23,_,ureply⟩ := fixed_chain o k s i ord left last r key
  have jj := j.isLt
  have sel : selectedWord i j<25 := by have:=salt_slot_bound (coord i).2;unfold selectedWord;omega
  unfold fixedOne
  rw [installs_salt _ i ord left l hi upc uregs u6 u28 u23 j, ureply ⟨selectedWord i j,sel⟩]
  exact congrFun (salt_slice_eq (chainReply o k i) (coord i).2) j

/-- The fixed outcome keeps the head's words outside word 128, the scratch and the salt. -/
theorem fixed_outside (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (l : 0<left) (hi : left≤16777216) (r : Input s i ord left last) (key : KeyWords s k) (w : Nat) (fit : w<2^33)
    (n128 : w≠128) (nsc : w<192 ∨ 217≤w) (ns : w≠1140851204+2*i.val ∧ w≠1140851204+2*i.val+1) :
    memoryView (fixedOne o s i left last) w=memoryView (fixedHead o s i last) w := by
  obtain ⟨upc,uregs,u6,u28,u23,uview,_⟩ := fixed_chain o k s i ord left last r key
  unfold fixedOne
  rw [post_outside _ i ord left l hi upc uregs u6 u28 u23 w fit ns, uview w fit n128 nsc]

theorem inverse_query_eq (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (fresh : i.val/4≠last) (even : i.val/4%2=0) :
    inverseQuery s i=packBuffer (window (memoryView s) (replyEWord (i.val/4))) := by
  have m := (head_even_pre s i ord left last r fresh even).2.2.1
  unfold inverseQuery
  congr 2; funext j
  exact view_eq_of_mem m _

/-- A new even quartet: the fixed outcome holds the inverse reply's d3 over reply_E. -/
theorem fixed_d3 (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (l : 0<left) (hi : left≤16777216) (r : Input s i ord left last) (key : KeyWords s k)
    (fresh : i.val/4≠last) (even : i.val/4%2=0) (m : Nat) (hm : m<4) :
    memoryView (fixedOne o s i left last) (replyEWord (i.val/4)+m)=
      replyWords (o.permutation.symm (packBuffer (window (memoryView s) (replyEWord (i.val/4))))) ⟨21+m,by omega⟩ := by
  have ix : i.val<16777216 := i.isLt
  rw [fixed_outside o k s i ord left last l hi r key _ (by unfold replyEWord blockWord; omega)
    (by unfold replyEWord blockWord; omega) (Or.inr (by unfold replyEWord blockWord; omega))
    ⟨by unfold replyEWord blockWord; omega,by unfold replyEWord blockWord; omega⟩]
  have inv : inverts i last=true := by simp [inverts,fresh,even]
  unfold fixedHead; rw [inv, if_pos rfl, head_d3 s i ord left last r _ fresh even m hm, fixedInverse,
    inverse_query_eq s i ord left last r fresh even]

/-- A new quartet: the fixed outcome holds the sibling group's node in its level-22 heap slot. -/
theorem fixed_sibling (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (l : 0<left) (hi : left≤16777216) (r : Input s i ord left last) (key : KeyWords s k)
    (fresh : i.val/4≠last) (m : Nat) (hm : m<4) :
    memoryView (fixedOne o s i left last) (heapWord (4194304+(i.val/4^^^1))+m)=
      memoryView s (nodeWordOf (i.val/4^^^1)+m) := by
  have ix : i.val<16777216 := i.isLt
  have gx := xor_one_lt (i.val/4) 22 (by omega) (by decide)
  rw [fixed_outside o k s i ord left last l hi r key _ (by unfold heapWord; omega) (by unfold heapWord; omega)
    (Or.inr (by unfold heapWord; omega)) ⟨by unfold heapWord; omega,by unfold heapWord; omega⟩]
  unfold fixedHead; exact head_sibling s i ord left last r _ fresh m hm

end TwoPermutationPrototype.GroupedOpening
