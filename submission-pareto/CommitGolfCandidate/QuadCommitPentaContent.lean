import CommitGolfCandidate.QuadCommitPentaLevel
import CommitGolfCandidate.TwoPermutationHeapInvariant

/-! Memory meaning of the level passes. `Tree s nodes salts L` says that the salts, the zero
prefixes of all groups of levels `0 … 10` and every slot (in range or ragged) of levels below `L`
are in place. A level pass for level `k+1` writes only its own slots, so it keeps the tree below
and adds level `k+1`. -/
namespace TwoPermutationPrototype.Quad.Commit.Penta
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure read_buffer_memory_congr
  write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] writeBits checkEvaluation

/-! ### The node input -/

theorem penta_input_zero_word (c : Fin 5 → BitVec 256) (k : Fin 5) :
    (pentaInput c).extractLsb' (64*k.val) 64=0 := by
  change ((((((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) ++ (0#320))).extractLsb' (64*k.val) 64=0
  rw [BitVec.extractLsb'_append_eq_of_add_le (by have := k.isLt;omega : 64*k.val+64≤320)]
  simp

theorem penta_input_digest_word (c : Fin 5 → BitVec 256) (slot : Fin 5) (k : Fin 4) :
    (pentaInput c).extractLsb' (64*(5+4*slot.val+k.val)) 64 = (c slot).extractLsb' (64*k.val) 64 := by
  change ((((((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) ++ (0#320))).extractLsb' (64*(5+4*slot.val+k.val)) 64 =
    (c slot).extractLsb' (64*k.val) 64
  have hk := k.isLt
  fin_cases slot <;> apply BitVec.eq_of_getLsbD_eq <;> intro bit hbit
  all_goals simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_append]
  all_goals simp only [show decide (bit<64)=true by exact decide_eq_true hbit,Bool.true_and]
  all_goals split_ifs <;> first | omega | (congr 1 <;> omega)

theorem penta_buffer_eq (s : MachineState) (k g : Nat) (c : Fin 5 → BitVec 256)
    (zeros : ∀ t : Fin 5, memoryView s (pentaGroupWord k g+t.val)=0)
    (children : ∀ (slot : Fin 5) (w : Fin 4), memoryView s (pentaGroupWord k g+5+4*slot.val+w.val)=
      (c slot).extractLsb' (64*w.val) 64) :
    readBuffer s (8*pentaGroupWord k g) 200=pentaInput c := by
  apply aligned_buffer_eq s _ 200 (by decide)
  intro w hw
  by_cases low : w<5
  · rw [zeros ⟨w,low⟩]
    exact (penta_input_zero_word c ⟨w,low⟩).symm
  · let slot : Fin 5 := ⟨(w-5)/4,by omega⟩
    let word : Fin 4 := ⟨(w-5)%4,Nat.mod_lt _ (by decide)⟩
    have offset : 5+4*slot.val+word.val=w := by dsimp [slot,word];omega
    have address : pentaGroupWord k g+w=pentaGroupWord k g+5+4*slot.val+word.val := by omega
    rw [address,children]
    have slice := penta_input_digest_word c slot word
    rw [offset] at slice
    exact slice.symm

/-- The slot of a group's child is the child's node slot. -/
theorem child_slot_word (k g : Nat) (t : Fin 5) (occ : slotBase k ≤ t.val) :
    pentaSlotWord k (childIndex k g t)=pentaGroupWord k g+5+4*t.val := by
  have ht := t.isLt
  unfold pentaSlotWord childIndex pentaGroupWord
  rcases radix_cases k with ⟨hr,hs⟩|⟨hr,hs⟩|⟨hr,hs⟩ <;> simp only [hr,hs] at occ ⊢ <;> omega

theorem buffer_digest_words (s : MachineState) (w : Nat) (d : BitVec 256)
    (read : readBuffer s (8*w) 32=d) (k : Fin 4) :
    memoryView s (w+k.val)=d.extractLsb' (64*k.val) 64 := by
  rw [←RV64.read_word]
  have slice := CommitGolfCandidate.read_buffer_slice s (8*w) 32 (8*k.val) 8 (by have := k.isLt;omega)
  rw [read] at slice
  rw [show 8*(w+k.val)=8*w+8*k.val by omega,←slice,←Nat.mul_assoc]

/-! ### The invariant -/

theorem prefix_before_slot (k j : Nat) : pentaGroupWord k (j/radix k)+prefixWords k ≤ pentaSlotWord k j := by
  unfold prefixWords pentaSlotWord; omega

/-- Slot `t` of level-`k` group `g` of the node table. -/
def groupChildren (nodes : Nat → Nat → BitVec 256) (k g : Nat) : Fin 5 → BitVec 256 :=
  fun t => if slotBase k ≤ t.val then nodes k (childIndex k g t) else 0

structure Tree (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (L : Nat) : Prop where
  nonce : ∀ (i : Index) (t : Fin 2), memoryView s (saltWord i.val+t.val)=(salts i).extractLsb' (64*t.val) 64
  zeros : ∀ k g, k≤12 → g<pentaCount (k+1) → ∀ t, t<prefixWords k → memoryView s (pentaGroupWord k g+t)=0
  node : ∀ k j, k<L → j<radix k*pentaCount (k+1) → ∀ t : Fin 4,
    memoryView s (pentaSlotWord k j+t.val)=(nodes k j).extractLsb' (64*t.val) 64

structure Partial (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (k j : Nat) : Prop
    extends Tree s nodes salts (k+1) where
  done : ∀ i, i<j → ∀ t : Fin 4,
    memoryView s (pentaSlotWord (k+1) i+t.val)=(nodes (k+1) i).extractLsb' (64*t.val) 64

theorem count_step (k : Nat) : pentaCount (k+1)=(pentaCount k+radix k-1)/radix k := rfl

theorem tree_same_mem (s u : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (L : Nat)
    (r : Tree s nodes salts L) (h : u.mem=s.mem) : Tree u nodes salts L := by
  have view : memoryView u=memoryView s := by funext w;change u.mem _=s.mem _;rw [h]
  exact ⟨by rw [view];exact r.nonce,by rw [view];exact r.zeros,by rw [view];exact r.node⟩

theorem partial_same_mem (s u : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (k j : Nat)
    (r : Partial s nodes salts k j) (h : u.mem=s.mem) : Partial u nodes salts k j := by
  have view : memoryView u=memoryView s := by funext w;change u.mem _=s.mem _;rw [h]
  exact ⟨tree_same_mem s u nodes salts (k+1) r.toTree h,by rw [view];exact r.done⟩

private theorem count_table : ∀ l : Fin 13, pentaCount (l.val+1)<2^24 := by decide

theorem count_lt (l : Nat) (hl : l≤12) : pentaCount (l+1)<2^24 := count_table ⟨l,by omega⟩

theorem salt_top (i : Index) : saltWord i.val+2≤2^33 := by
  have : i.val<16777216 := i.isLt
  unfold saltWord
  omega

theorem group_top (l g : Nat) (hl : l≤12) (hg : g<pentaCount (l+1)) : pentaGroupWord l g+46≤2^33 := by
  have := count_lt l hl
  exact group_room l g (by omega)

/-- The group of a node in range is in range. -/
theorem group_inside (k j : Nat) (hj : j<radix k*pentaCount (k+1)) : j/radix k<pentaCount (k+1) := by
  have := radix_pos k
  exact Nat.div_lt_of_lt_mul hj

/-- A write of the 25 words from a level-`l` slot misses every zero prefix. -/
theorem write_misses_prefix (l j m g : Nat) (hl : l≤13) (hm : m≤13) (hj : j/radix l<pentaCount (l+1))
    (hg : g<pentaCount (m+1)) (t : Nat) (ht : t<prefixWords m) :
    pentaGroupWord m g+t<pentaSlotWord l j ∨ pentaSlotWord l j+25≤pentaGroupWord m g+t := by
  have writeEnd := slot_write_end l j
  have start := prefix_before_slot l j
  have pw := prefix_words_le m
  have e : pentaGroupWord l (j/radix l+1)=pentaGroupWord l (j/radix l)+46 := by unfold pentaGroupWord;omega
  by_cases same : m=l
  · subst same
    by_cases earlier : j/radix m<g
    · right
      have : pentaGroupWord m (j/radix m+1)≤pentaGroupWord m g := by unfold pentaGroupWord;omega
      omega
    · left
      by_cases eq : g=j/radix m
      · subst eq; omega
      · have : pentaGroupWord m g+46≤pentaGroupWord m (j/radix m) := by unfold pentaGroupWord;omega
        omega
  · by_cases lower : m<l
    · have := level_order m l g lower hl hg (j/radix l)
      left;omega
    · have := level_order l m (j/radix l) (by omega) hm hj g
      right;omega

/-- A node in range lies in a group in range of the level above. -/
theorem next_group_inside (k j : Nat) (inside : j<pentaCount (k+1)) : j/radix (k+1)<pentaCount (k+2) := by
  rw [count_step (k+1)]
  rcases radix_cases (k+1) with ⟨hr,_⟩|⟨hr,_⟩|⟨hr,_⟩ <;> simp only [hr] <;> omega

/-- A write that only touches level-`k+1` words from slot `j` on keeps the partial level. -/
theorem partial_frame (s u : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (k j : Nat) (hk : k≤11) (inside : j<pentaCount (k+1)) (r : Partial s nodes salts k j)
    (frame : ∀ w, w<pentaSlotWord (k+1) j ∨ pentaSlotWord (k+1) j+25≤w → w<2^33 →
      memoryView u w=memoryView s w) :
    Partial u nodes salts k j := by
  have groupInside := next_group_inside k j inside
  have writeEnd := slot_write_end (k+1) j
  have e : pentaGroupWord (k+1) (j/radix (k+1)+1)=pentaGroupWord (k+1) (j/radix (k+1))+46 := by
    unfold pentaGroupWord;omega
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro i t
    have below := group_below_salts (k+1) (j/radix (k+1)) (by omega) groupInside i.val
    have top := salt_top i
    have := t.isLt
    rw [frame _ (Or.inr (by omega)) (by omega)]
    exact r.nonce i t
  · intro l g hl hg t ht
    have room := group_top l g hl hg
    have := prefix_words_le l
    rw [frame _ (write_misses_prefix (k+1) j l g (by omega) (by omega) groupInside hg t ht) (by omega)]
    exact r.zeros l g hl hg t ht
  · intro l i hl hi t
    have := t.isLt
    have groupI := group_inside l i hi
    have order := level_order l (k+1) (i/radix l) (by omega) (by omega) groupI (j/radix (k+1))
    have slotEnd := slot_write_end l i
    have room := group_top l (i/radix l) (by omega) groupI
    have e' : pentaGroupWord l (i/radix l+1)=pentaGroupWord l (i/radix l)+46 := by unfold pentaGroupWord;omega
    have start := prefix_before_slot (k+1) j
    rw [frame _ (Or.inl (by omega)) (by omega)]
    exact r.node l i hl hi t
  · intro i hi t
    have := t.isLt
    have sep := slot_separate (k+1) i j hi
    have room := slot_room (k+1) j (by have := count_lt k (by omega);omega)
    rw [frame _ (Or.inl (by omega)) (by omega)]
    exact r.done i hi t

/-- Node values: in-range nodes are the node function of their group, the others are zero. -/
structure Values (oracle : Oracle) (nodes : Nat → Nat → BitVec 256) : Prop where
  value : ∀ k j, j<pentaCount (k+1) →
    nodes (k+1) j=pentaFunction oracle.permutation (groupChildren nodes k j)
  ragged : ∀ k j, pentaCount k≤ j → nodes k j=0

theorem child_index_lt (k g : Nat) (t : Fin 5) (hg : g<pentaCount (k+1)) :
    childIndex k g t<radix k*pentaCount (k+1) := by
  have ht := t.isLt
  unfold childIndex
  rcases radix_cases k with ⟨hr,hs⟩|⟨hr,hs⟩|⟨hr,hs⟩ <;> simp only [hr,hs] <;> omega

theorem node_input (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (k j : Nat)
    (hk : k≤12) (inside : j<pentaCount (k+1)) (r : Tree s nodes salts (k+1)) :
    readBuffer s (8*pentaGroupWord k j) 200=pentaInput (groupChildren nodes k j) := by
  apply penta_buffer_eq s k j _ (fun t => r.zeros k j hk inside t.val (by unfold prefixWords;omega))
  intro slot w
  unfold groupChildren
  split
  · rename_i occ
    rw [←child_slot_word k j slot occ]
    exact r.node k _ (by omega) (child_index_lt k j slot inside) w
  · rename_i free
    rw [show pentaGroupWord k j+5+4*slot.val+w.val=pentaGroupWord k j+(5+4*slot.val+w.val) by omega,
      r.zeros k j hk inside _ (by unfold prefixWords;have := w.isLt;omega)]
    simp

theorem content_step (oracle : Oracle) (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (v : Values oracle nodes) (k j : Nat) (hk : k≤11) (inside : j<pentaCount (k+1))
    (r : Partial s nodes salts k j) :
    Partial (after k s j (oracle.permutation (packBuffer (window (memoryView s) (pentaGroupWord k j)))))
      nodes salts k (j+1) := by
  let reply := oracle.permutation (packBuffer (window (memoryView s) (pentaGroupWord k j)))
  have countBound : pentaCount (k+1)<2^24 := count_lt k (by omega)
  have mem : (after k s j reply).mem=(writeBits s (wordAddress (pentaSlotWord (k+1) j)) reply).mem := by unfold after;rfl
  have view : ∀ w, w<2^33 → memoryView (after k s j reply) w =
      writeWindow (memoryView s) (pentaSlotWord (k+1) j) (replyWords reply) w := by
    intro w hw
    rw [show memoryView (after k s j reply) w=memoryView (writeBits s (wordAddress (pentaSlotWord (k+1) j)) reply) w by
      change (after k s j reply).mem _=_;rw [mem];rfl]
    exact permutation_write_memory s _ w reply (slot_room (k+1) j (by omega)) hw
  have kept := partial_frame s (after k s j reply) nodes salts k j hk inside r (by
    intro w away hw
    rw [view w hw]
    unfold writeWindow
    rw [dif_neg (by omega)])
  refine ⟨kept.toTree,?_⟩
  intro i hi t
  by_cases same : i=j
  · subst i
    have written := write_bits_digest (bits := 1600) s (8*pentaSlotWord (k+1) j) 0 reply (by decide) (by decide)
    simp only [Nat.mul_zero,Nat.add_zero] at written
    have buffer : readBuffer (after k s j reply) (8*pentaSlotWord (k+1) j) 32=nodes (k+1) j := by
      rw [read_buffer_memory_congr _ _ mem]
      apply written.trans
      rw [v.value k j inside]
      unfold reply pentaFunction
      rw [←read_permutation_window,node_input s nodes salts k j (by omega) inside r.toTree]
      rfl
    exact buffer_digest_words _ _ _ buffer t
  · exact kept.done i (by omega) t

theorem sequence_content (oracle : Oracle) (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (v : Values oracle nodes) (k count j : Nat) (hk : k≤11) (limit : j+count≤pentaCount (k+1))
    (r : Partial s nodes salts k j) :
    Partial (checkEvaluation oracle (trace k count j s)).1 nodes salts k (j+count) := by
  induction count generalizing s j with
  | zero => simpa only [trace,check_evaluation_pure,Nat.add_zero] using r
  | succ c ih =>
    rw [trace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (pentaGroupWord k j))))))) :
        OracleComp World (BitVec 1600)) =
      (oracle.permutation (packBuffer (window (memoryView s) (pentaGroupWord k j))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    have step := content_step oracle s nodes salts v k j hk (by omega) r
    have tail := ih _ (j+1) (by omega) step
    rwa [show j+1+c=j+(c+1) by omega] at tail

theorem loops_content (oracle : Oracle) (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (v : Values oracle nodes) (k B S cnt j : Nat) (hk : k≤11) (limit : j+S*cnt≤pentaCount (k+1))
    (r : Partial s nodes salts k j) :
    Partial (checkEvaluation oracle (loops k B S cnt j s)).1 nodes salts k (j+S*cnt) := by
  induction cnt generalizing s j with
  | zero => simpa only [loops,check_evaluation_pure,Nat.mul_zero,Nat.add_zero] using r
  | succ c ih =>
    rw [loops,check_evaluation_bind]
    have body := sequence_content oracle s nodes salts v k S j hk (by rw [Nat.mul_succ] at limit;omega) r
    let mid := (checkEvaluation oracle (trace k S j s)).1
    have next := partial_same_mem mid (mid.setPC (nextPC B S c)) nodes salts k (j+S) body rfl
    have tail := ih _ (j+S) (by rw [Nat.mul_succ] at limit;omega) next
    rwa [show j+S+S*c=j+S*(c+1) by rw [Nat.mul_succ];omega] at tail

theorem count_le (k : Nat) : pentaCount k≤radix k*pentaCount (k+1) := by
  rw [count_step k]
  rcases radix_cases k with ⟨hr,_⟩|⟨hr,_⟩|⟨hr,_⟩ <;> simp only [hr] <;> omega

theorem full_group (k : Nat) (h : pentaCount k%radix k=0) : radix k*pentaCount (k+1)=pentaCount k := by
  rw [count_step k]
  rcases radix_cases k with ⟨hr,_⟩|⟨hr,_⟩|⟨hr,_⟩ <;> simp only [hr] at h ⊢ <;> omega

theorem last_group (k : Nat) (h : pentaCount k%radix k≠0) : pentaCount (k+1)=pentaCount k/radix k+1 := by
  rw [count_step k]
  rcases radix_cases k with ⟨hr,_⟩|⟨hr,_⟩|⟨hr,_⟩ <;> simp only [hr] at h ⊢ <;> omega

/-- Clearing the ragged slots completes level `k+1`. -/
theorem zero_content (oracle : Oracle) (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (v : Values oracle nodes) (k z : Nat) (hk : k≤11) (r : Partial s nodes salts k (pentaCount (k+1)))
    (x12 : s.getReg .x12=wordAddress (pentaSlotWord (k+1) (pentaCount (k+1))))
    (ragged : z=4*(radix (k+1)*pentaCount (k+2)-pentaCount (k+1))) (small : 8*z<2048) :
    Tree (zeroed s 0 z z) nodes salts (k+2) := by
  have countBound := count_lt k (by omega)
  have le : pentaCount (k+1)≤radix (k+1)*pentaCount (k+2) := count_le (k+1)
  have sum := slot_base_add (k+1)
  have rpos := radix_pos (k+1)
  by_cases none : z=0
  · subst none
    have full : radix (k+1)*pentaCount (k+2)=pentaCount (k+1) := by omega
    refine ⟨r.nonce,r.zeros,?_⟩
    intro l i hl hi t
    by_cases same : l=k+1
    · subst same
      have hi' : i<radix (k+1)*pentaCount (k+2) := hi
      exact r.done i (by omega) t
    · exact r.node l i (by omega) hi t
  have notFull : pentaCount (k+1)%radix (k+1)≠0 := by
    intro h
    have this : radix (k+1)*pentaCount (k+2)=pentaCount (k+1) := full_group (k+1) h
    omega
  have lastG : pentaCount (k+2)=pentaCount (k+1)/radix (k+1)+1 := last_group (k+1) notFull
  have dm := Nat.div_add_mod (pentaCount (k+1)) (radix (k+1))
  have modLt := Nat.mod_lt (pentaCount (k+1)) rpos
  have mulExp : radix (k+1)*(pentaCount (k+1)/radix (k+1)+1)=
      radix (k+1)*(pentaCount (k+1)/radix (k+1))+radix (k+1) := by rw [Nat.mul_add,Nat.mul_one]
  have slotLow : pentaSlotWord (k+1) (pentaCount (k+1))<2^31 := by
    have := base_word_le (k+1)
    unfold pentaSlotWord pentaGroupWord
    rcases radix_cases (k+1) with ⟨hr,hs⟩|⟨hr,hs⟩|⟨hr,hs⟩ <;> simp only [hr,hs] <;> omega
  have view : ∀ w, w<2^33 → memoryView (zeroed s 0 z z) w =
      if pentaSlotWord (k+1) (pentaCount (k+1))≤w ∧ w<pentaSlotWord (k+1) (pentaCount (k+1))+z then 0
      else memoryView s w := by
    intro w hw
    have := zeroed_memory s 0 z z (pentaSlotWord (k+1) (pentaCount (k+1))) le_rfl x12 (by decide) (by omega)
      (by omega) w hw
    simpa using this
  have outside : ∀ w, w<pentaSlotWord (k+1) (pentaCount (k+1)) ∨ pentaSlotWord (k+1) (pentaCount (k+1))+z≤w →
      w<2^33 → memoryView (zeroed s 0 z z) w=memoryView s w := by
    intro w away hw
    rw [view w hw,if_neg (by omega)]
  have startW : pentaSlotWord (k+1) (pentaCount (k+1))=pentaGroupWord (k+1) (pentaCount (k+1)/radix (k+1))+5+
      4*(slotBase (k+1)+pentaCount (k+1)%radix (k+1)) := rfl
  have endW : pentaSlotWord (k+1) (pentaCount (k+1))+z=pentaGroupWord (k+1) (pentaCount (k+1)/radix (k+1))+25 := by
    rw [startW,ragged,lastG,mulExp]
    omega
  have lastBound : pentaCount (k+1)/radix (k+1)<pentaCount (k+2) := by omega
  have pre := prefix_words_le (k+1)
  refine ⟨?_,?_,?_⟩
  · intro i t
    have below := group_below_salts (k+1) (pentaCount (k+1)/radix (k+1)) (by omega) lastBound i.val
    have top := salt_top i
    have := t.isLt
    rw [outside _ (Or.inr (by omega)) (by omega)]
    exact r.nonce i t
  · intro l g hl hg t ht
    have room := group_top l g hl hg
    have := prefix_words_le l
    have miss := write_misses_prefix (k+1) (pentaCount (k+1)) l g (by omega) (by omega) lastBound hg t ht
    rw [outside _ (by omega) (by omega)]
    exact r.zeros l g hl hg t ht
  · intro l i hl hi t
    have := t.isLt
    by_cases same : l=k+1
    · subst same
      by_cases real : i<pentaCount (k+1)
      · have sep := slot_separate (k+1) i (pentaCount (k+1)) real
        rw [outside _ (Or.inl (by omega)) (by omega)]
        exact r.done i real t
      · have hi' : i<radix (k+1)*(pentaCount (k+1)/radix (k+1)+1) := by
          rw [←lastG]; exact hi
        have hup : i / radix (k+1) < pentaCount (k+1) / radix (k+1) + 1 := Nat.div_lt_of_lt_mul hi'
        have hdown : pentaCount (k+1) / radix (k+1) ≤ i / radix (k+1) := Nat.div_le_div_right (by omega)
        have sameG : i/radix (k+1)=pentaCount (k+1)/radix (k+1) := by omega
        have dmi := Nat.div_add_mod i (radix (k+1))
        have modI := Nat.mod_lt i rpos
        rw [sameG] at dmi
        have inRegion : pentaSlotWord (k+1) (pentaCount (k+1))≤pentaSlotWord (k+1) i+t.val ∧
            pentaSlotWord (k+1) i+t.val<pentaSlotWord (k+1) (pentaCount (k+1))+z := by
          rw [endW,startW]
          unfold pentaSlotWord
          rw [sameG]
          omega
        rw [view _ (by omega),if_pos inRegion,v.ragged (k+1) i (by omega)]
        simp
    · have lower : l<k+1 := by omega
      have groupI := group_inside l i hi
      have order := level_order l (k+1) (i/radix l) lower (by omega) groupI (pentaCount (k+1)/radix (k+1))
      have slotEnd := slot_write_end l i
      have room := group_top l (i/radix l) (by omega) groupI
      have e : pentaGroupWord l (i/radix l+1)=pentaGroupWord l (i/radix l)+46 := by unfold pentaGroupWord;omega
      have start := prefix_before_slot (k+1) (pentaCount (k+1))
      rw [outside _ (Or.inl (by omega)) (by omega)]
      exact r.node l i (by omega) hi t

end TwoPermutationPrototype.Quad.Commit.Penta
