import CommitGolfCandidate.ChainedRootContent
import CommitGolfCandidate.ChainedFastValues
import CommitGolfCandidate.ChainedFastPhase

/-! Heap content through the specialized heights. Below the cursor `n`, the children of
parents `≤ n` may still carry their unmasked top word; every other slot above `n` holds its
reference digest. The hand-over at `2^16-1` gives the delivered `HeapContent`. -/
namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
attribute [local irreducible] execute nodeSteps

def leafH : Height := ⟨16,by decide⟩
def view (i : Nat) (x : Output) : Output := if 2^24 ≤ i then finalValue leafH x else finalValue 0 x
/-- Leaves as the leaf phase leaves them: the top word still carries bits above 238. -/
def RawLeaves (s : MachineState) (heap : Nat → BitVec 238) : Prop :=
  ∀ i, 2^24 ≤ i → i < 2^25 → finalValue leafH (heapDigest s i) = (heap i).setWidth 256
def logical (heap : Nat → BitVec 238) (i : Nat) : Output := (heap i).setWidth 256
def phys (s : MachineState) (i : Nat) : Output := heapDigest s i
attribute [local irreducible] readBuffer heapDigest phys

structure Inv (heap : Nat → BitVec 238) (s : MachineState) (cursor : Nat) : Prop where
  front : Frontier view (logical heap) (phys s) cursor
  stable : ∀ i, cursor < i → i < 2^17 → view i (phys s i) = phys s i

theorem count_zero : count 0=8388608 := by decide +kernel
theorem count_inner : ∀ h : Low, h.val≠0 → count h≤4194304 := by decide +kernel
theorem count_seven : ∀ h : Low, count h<131072 → h.val=7 := by decide +kernel

theorem final_low (h : Low) : finalValue (height h)=finalValue 0 := by
  funext v;fin_cases h <;> rfl
theorem mask_low : finalMask 0=W (2^42-1) := by decide
theorem width_low (h : Low) : finalMask (height h)=finalMask 0 := by fin_cases h <;> rfl

theorem eval_bind_fst (o : Oracle) {α β : Type} (p : OracleComp World α) (f : α → OracleComp World β) :
    (checkEvaluation o (p >>= f)).1=(checkEvaluation o (f (checkEvaluation o p).1)).1 := by
  rw [check_evaluation_bind]
theorem eval_pure_fst (o : Oracle) {α : Type} (a : α) : (checkEvaluation o (pure a)).1=a := by
  rw [check_evaluation_pure]
theorem eval_query_fst (o : Oracle) {α : Type} (q : PublicSpec.Domain)
    (f : PublicSpec.Range q → OracleComp World α) :
    (checkEvaluation o ((liftM (World.query (.inr q)) : OracleComp World _) >>= f)).1=
      (checkEvaluation o (f (o.answer (m:=Id) q))).1 := by
  rw [check_evaluation_public_bind]

theorem parent_value_replies (o : Oracle) (h : Low) (L R : BitVec 238) :
    parentValue o (height h) L R=finalValue (height h) (replies o h L R 3) := by
  have c : calls (height h)-1=3 := by fin_cases h <;> rfl
  unfold parentValue parentDigestTrace
  rw [c]
  simp only [continuationTrace,bind_assoc,eval_query_fst,eval_pure_fst]
  rfl

/-! Words of one digest. -/

theorem word_of (s : MachineState) (i k : Nat) (hk : k<4) (hi : i<2^25) :
    (phys s i).extractLsb' (64*k) 64=s.getMem (W (heapBase+32*i+8*k)) := by
  unfold phys heapDigest
  exact read_digest_word s _ k (by unfold heapBase;omega) hk

theorem digest_eq {s t : MachineState} {i j : Nat} (hi : i<2^25) (hj : j<2^25)
    (w : ∀ k<4,t.getMem (W (heapBase+32*j+8*k))=s.getMem (W (heapBase+32*i+8*k))) : phys t j=phys s i := by
  apply output_ext_words;intro k
  rw [word_of t j k.val k.isLt hj,word_of s i k.val k.isLt hi,w k.val k.isLt]

theorem final_word (v : Output) (k : Nat) (hk : k<4) :
    (finalValue 0 v).extractLsb' (64*k) 64=if k=3 then v.extractLsb' 192 64 &&& W (2^42-1)
      else v.extractLsb' (64*k) 64 := by
  by_cases k3 : k=3
  · subst k3;rw [if_pos rfl,←mask_low];exact final_top_word 0 v
  · rw [if_neg k3];exact final_low_word 0 v k (by omega)

theorem final_wordH (H : Height) (v : Output) (k : Nat) (hk : k<4) :
    (finalValue H v).extractLsb' (64*k) 64=if k=3 then v.extractLsb' 192 64 &&& finalMask H
      else v.extractLsb' (64*k) 64 := by
  by_cases k3 : k=3
  · subst k3;rw [if_pos rfl];exact final_top_word H v
  · rw [if_neg k3];exact final_low_word H v k (by omega)

def kidH (h : Low) : Height := if h.val=0 then leafH else 0
theorem mask_kid (h : Low) : childMaskW h=finalMask (kidH h) := by
  unfold childMaskW kidH;split <;> decide
theorem view_kid (h : Low) (n c : Nat) (lo : count h≤n) (hi : n<2*count h) (hc : c<2) (x : Output) :
    view (2*n+c) x=finalValue (kidH h) x := by
  unfold view kidH
  by_cases h0 : h.val=0
  · have e : h=0:=Fin.ext h0;subst e;have:=count_zero;rw [if_pos (by omega)];rfl
  · have:=count_inner h h0;rw [if_neg (by omega),if_neg h0]

theorem final_idem (v : Output) : finalValue 0 (finalValue 0 v)=finalValue 0 v := by
  apply output_ext_words;intro k
  rw [final_word _ k.val k.isLt,final_word _ k.val k.isLt,final_word _ 3 (by decide)]
  split <;> simp [BitVec.and_assoc]

/-! The slots of node `n`, as heap words. -/

theorem child_slot (n : Nat) (i : Fin 8) : address n (cslot i)=heapBase+32*(2*n+i.val/4)+8*(i.val%4) := by
  have:=i.isLt;unfold address cslot;simp;omega
theorem parent_slot (n : Nat) (k : Fin 4) : address n ⟨8+k.val,by omega⟩=heapBase+32*n+8*k.val := by
  have:=k.isLt;unfold address;simp;omega

/-- What one node leaves in memory, in terms of its replies (from `node_memory`). -/
structure NodeOut (o : Oracle) (h : Low) (n : Nat) (s t : MachineState) (L R : BitVec 238) : Prop where
  mem : ∀ i, t.getMem (W (address n i))=interp s n (replies o h L R) (outputExpr h i)
  frame : ∀ q : Nat,q%8=0 → q+32≤2^64 → (∀ i:Slot,q≠address n i) → t.getMem (W q)=s.getMem (W q)

theorem node_words (heap : Nat → BitVec 238) (h : Low) (n : Nat) (lo : count h≤n) (hi : n<2*count h)
    (s : MachineState) (band : Band h s) (inv : Inv heap s n) :
    CanonicalWords s n h (heap (2*n)) (heap (2*n+1)) := by
  have sz:=count_size h
  intro i
  have ci:=child_slot n i
  have c : i.val/4<2 := by have:=i.isLt;omega
  have w:=word_of s (2*n+i.val/4) (i.val%4) (by omega) (by omega)
  have v0:=inv.front (2*n+i.val/4) (by omega) (by omega)
  rw [if_pos (by omega)] at v0
  have ext (x : BitVec 238) (k : Nat) (hk : k<4) := child_word_extended x k hk
  have goalR : (if i.val<4 then childWord (heap (2*n)) i.val else childWord (heap (2*n+1)) (i.val-4))=
      (logical heap (2*n+i.val/4)).extractLsb' (64*(i.val%4)) 64 := by
    unfold logical
    split <;> rename_i lt
    · rw [show i.val/4=0 by omega,show i.val%4=i.val by omega,Nat.add_zero];exact (ext _ _ lt).symm
    · rw [show i.val/4=1 by omega,show i.val%4=i.val-4 by omega];exact (ext _ _ (by have:=i.isLt;omega)).symm
  rw [goalR,←v0,view_kid h n (i.val/4) lo hi c,final_wordH _ _ _ (by omega),w,←ci]
  unfold childExpr
  by_cases top : i.val=3 ∨ i.val=7
  · have k3 : i.val%4=3 := by omega
    rw [if_pos top,if_pos k3]
    show s.getMem (W (address n (cslot i))) &&& s.getReg .x3=_
    rw [band.childMaskReg,mask_kid,ci,k3,←word_of s _ 3 (by decide) (by omega)]
  · have k3 : i.val%4≠3 := by have:=i.isLt;omega
    rw [if_neg top,if_neg k3]
    show s.getMem (W (address n (cslot i)))=_
    rw [ci,←word_of s _ _ (by omega) (by omega)]

theorem parent_word (o : Oracle) (h : Low) (n : Nat) (s t : MachineState) (L R : BitVec 238)
    (out : NodeOut o h n s t L R) (band : Band h s) (k : Nat) (hk : k<4) :
    t.getMem (W (heapBase+32*n+8*k))=
      if h.val=7 ∧ k=3 then (replies o h L R 3).extractLsb' 192 64 &&& W (2^42-1)
      else (replies o h L R 3).extractLsb' (64*k) 64 := by
  have m:=out.mem ⟨8+k,by omega⟩
  rw [parent_slot n ⟨k,hk⟩] at m
  rw [m];unfold outputExpr
  rw [dif_neg (by simp),dif_pos (by simp;omega)]
  by_cases e : h.val=7 ∧ k=3
  · have c : h.val=7 ∧ 8+k=11 := ⟨e.1,by omega⟩
    rw [if_pos c,if_pos e]
    show ew (replies o h L R 3) ⟨8+k-8,_⟩ &&& s.getReg .x15=_
    rw [band.parentMaskReg e.1]
    simp only [ew,e.2,Nat.add_sub_cancel_left]
  · have c : ¬(h.val=7 ∧ 8+k=11) := fun x=>e ⟨x.1,by omega⟩
    rw [if_neg c,if_neg e]
    show ew (replies o h L R 3) ⟨8+k-8,_⟩=_
    simp only [ew,Nat.add_sub_cancel_left]

theorem parent_final (o : Oracle) (heap : Nat → BitVec 238) (tree : ChainedTree o heap) (h : Low) (n : Nat)
    (lo : count h≤n) (hi : n<2*count h) (s t : MachineState) (band : Band h s)
    (out : NodeOut o h n s t (heap (2*n)) (heap (2*n+1))) :
    finalValue 0 (phys t n)=logical heap n := by
  have sz:=count_size h
  have lg : logical heap n=finalValue 0 (replies o h (heap (2*n)) (heap (2*n+1)) 3) := by
    unfold logical
    rw [tree (height h) n lo hi,parent_value_replies,final_low]
  rw [lg];apply output_ext_words;intro k
  rw [final_word _ k.val k.isLt,final_word _ k.val k.isLt]
  by_cases k3 : k.val=3
  · rw [if_pos k3,if_pos k3]
    have w:=word_of t n 3 (by decide) (by omega)
    rw [show (64*3:Nat)=192 from rfl] at w
    rw [w,parent_word o h n s t _ _ out band 3 (by decide)]
    split <;> simp [BitVec.and_assoc]
  · rw [if_neg k3,if_neg k3,word_of t n k.val k.isLt (by omega),parent_word o h n s t _ _ out band k.val k.isLt,
      if_neg (fun x=>k3 x.2)]

theorem parent_stable (o : Oracle) (h : Low) (n : Nat) (h7 : h.val=7) (small : n<2^24) (s t : MachineState)
    (L R : BitVec 238) (band : Band h s) (out : NodeOut o h n s t L R) : view n (phys t n)=phys t n := by
  rw [view,if_neg (by omega)];apply output_ext_words;intro k
  rw [final_word _ k.val k.isLt]
  by_cases k3 : k.val=3
  · rw [if_pos k3]
    have w:=word_of t n 3 (by decide) (by omega)
    rw [show (64*3:Nat)=192 from rfl] at w
    rw [k3,show (64*3:Nat)=192 from rfl,w,parent_word o h n s t _ _ out band 3 (by decide),if_pos ⟨h7,rfl⟩,
      BitVec.and_assoc,BitVec.and_self]
  · rw [if_neg k3]

theorem child_after (o : Oracle) (h : Low) (n : Nat) (lo : count h≤n) (hi : n<2*count h) (s t : MachineState)
    (L R : BitVec 238) (band : Band h s) (out : NodeOut o h n s t L R) (c : Nat) (hc : c<2) :
    phys t (2*n+c)=view (2*n+c) (phys s (2*n+c)) := by
  have sz:=count_size h
  apply output_ext_words;intro k
  let j : Fin 8 := ⟨4*c+k.val,by omega⟩
  have slot:=child_slot n j
  rw [show j.val/4=c by simp [j] <;> omega,show j.val%4=k.val by simp [j] <;> omega] at slot
  have m:=out.mem (cslot j)
  rw [slot] at m
  rw [word_of t (2*n+c) k.val k.isLt (by omega),m]
  unfold outputExpr
  rw [dif_pos (by simp [cslot,j];omega)]
  have back : (⟨(cslot j).val,by simp [cslot,j];omega⟩ : Fin 8)=j := by apply Fin.ext;simp [cslot]
  rw [back]
  rw [view_kid h n c lo hi hc,final_wordH _ _ k.val k.isLt]
  unfold childExpr
  by_cases top : j.val=3 ∨ j.val=7
  · have k3 : k.val=3 := by simp [j] at top;omega
    rw [if_pos top,if_pos k3]
    show s.getMem (W (address n (cslot j))) &&& s.getReg .x3=_
    rw [band.childMaskReg,mask_kid,child_slot,show j.val/4=c by simp [j] <;> omega,
      show j.val%4=k.val by simp [j] <;> omega,k3,←word_of s _ 3 (by decide) (by omega)]
  · have k3 : k.val≠3 := by intro e;apply top;simp [j];omega
    rw [if_neg top,if_neg k3]
    show s.getMem (W (address n (cslot j)))=_
    rw [child_slot,show j.val/4=c by simp [j] <;> omega,show j.val%4=k.val by simp [j] <;> omega,
      ←word_of s _ k.val k.isLt (by omega)]

theorem other_after (o : Oracle) (h : Low) (n : Nat) (s t : MachineState) (L R : BitVec 238)
    (out : NodeOut o h n s t L R) (i : Nat) (hi1 : n < i) (hi2 : i < 2^25) (l : i ≠ 2*n) (r : i ≠ 2*n+1) :
    phys t i=phys s i := by
  apply digest_eq hi2 hi2;intro k hk
  apply out.frame _ (by unfold heapBase;omega) (by unfold heapBase;omega)
  intro j e;unfold address heapBase at e;split_ifs at e <;> omega

theorem node_out (o : Oracle) (heap : Nat → BitVec 238) (h : Low) (n : Nat) (lo : count h≤n) (hi : n<2*count h)
    (s : MachineState) (band : Band h s) (inv : Inv heap s n) :
    NodeOut o h n s (checkEvaluation o (trace n (plan h) s)).1 (heap (2*n)) (heap (2*n+1)) := by
  have sz:=count_size h
  have b : Bounds n := ⟨by omega,by omega⟩
  have words:=node_words heap h n lo hi s band inv
  have tg : Tags s h := ⟨band.ht,band.tag0,band.tag1,band.tag2,band.z0,band.z1,band.flag⟩
  exact ⟨node_memory o h s n b _ _ words tg,(node_matches o h s n b _ _ words tg).frame⟩

theorem node_step (o : Oracle) (heap : Nat → BitVec 238) (tree : ChainedTree o heap) (h : Low) (n : Nat)
    (lo : count h≤n) (hi : n<2*count h) (s : MachineState) (band : Band h s) (inv : Inv heap s n) :
    Inv heap (checkEvaluation o (trace n (plan h) s)).1 (n-1) := by
  have sz:=count_size h
  have out:=node_out o heap h n lo hi s band inv
  refine ⟨frontier_step (by omega) (by omega) inv.front ?_ ?_ ?_ ?_,?_⟩
  · rw [view,if_neg (by omega)];exact parent_final o heap tree h n lo hi s _ band out
  · simpa using child_after o h n lo hi s _ _ _ band out 0 (by decide)
  · exact child_after o h n lo hi s _ _ _ band out 1 (by decide)
  · intro i a b l r;exact other_after o h n s _ _ _ out i a b l r
  · intro i lo' hi'
    by_cases e : i=n
    · rw [e];exact parent_stable o h n (count_seven h (by omega)) (by omega) s _ _ _ band out
    · rw [other_after o h n s _ _ _ out i (by omega) (by omega) (by omega) (by omega)]
      exact inv.stable i (by omega) hi'

/-! Memory-preserving control steps keep the invariant. -/

theorem phys_of_mem {s t : MachineState} (e : t.mem=s.mem) (i : Nat) : phys t i=phys s i := by
  unfold phys heapDigest
  exact read_digest_congr t s _ (by unfold heapBase;omega) (fun k _=>by simp [MachineState.getMem,e])

theorem Inv.of_mem {heap : Nat → BitVec 238} {s t : MachineState} {c : Nat} (inv : Inv heap s c) (e : t.mem=s.mem) :
    Inv heap t c := by
  have p:=phys_of_mem e
  refine ⟨fun i a b=>by rw [p i];exact inv.front i a b,fun i a b=>by rw [p i];exact inv.stable i a b⟩

/-! Lanes, groups, heights. -/

theorem lanes_inv (o : Oracle) (heap : Nat → BitVec 238) (tree : ChainedTree o heap) (h : Low) (G : Nat)
    (lo : 65536+15≤G) (hi : G<2^24) (inLevel : count h+15≤G ∧ G<2*count h) :
    ∀ r, r≤16 → ∀ s, Cursor h G s → s.pc=pc (lanePC h (16-r)) → Inv heap s (G-(16-r)) →
      Inv heap (checkEvaluation o (lanes h G r s)).1 (G-16) := by
  intro r
  induction r with
  | zero => intro _ s _ _ inv;rw [show lanes h G 0 s=pure s from rfl,eval_pure_fst];simpa using inv
  | succ r ih =>
    intro small s c here inv
    let k : Lane := ⟨15-r,by omega⟩
    have hk : lanePC h k.val=lanePC h (16-(r+1)) := by congr 1 <;> simp [k] <;> omega
    rw [show lanes h G (r+1) s=(trace (G-(15-r)) (plan h) s >>= lanes h G r) from rfl,eval_bind_fst]
    let mid:=(checkEvaluation o (trace (G-(15-r)) (plan h) s)).1
    have post:=lane_post h G k lo hi s mid c (here.trans (by rw [hk])) (check_evaluation_support o _)
    have step:=node_step o heap tree h (G-(15-r)) (by omega) (by omega) s c.toBand
      (by rw [show G-(15-r)=G-(16-(r+1)) by omega];exact inv)
    exact ih (by omega) mid post.1 (post.2.trans (by congr 2 <;> simp [k] <;> omega))
      (by rw [show G-(16-r)=G-(15-r)-1 by omega];exact step)

theorem groups_inv (o : Oracle) (heap : Nat → BitVec 238) (tree : ChainedTree o heap) (h : Low) :
    ∀ g, 1≤g → g≤groupsN h → ∀ s, Cursor h (groupBase h g) s → s.pc=pc (lanePC h 0) →
      Inv heap s (groupBase h g) → Inv heap (checkEvaluation o (groups h g s)).1 (groupBase h 0) := by
  intro g
  induction g with
  | zero => intro one;omega
  | succ g ih =>
    intro _ le s c here inv
    have sz:=count_size h
    have bd:=group_bounds h (g+1) (by omega) le
    rw [groups_succ,eval_bind_fst]
    let mid:=(checkEvaluation o (lanes h (groupBase h (g+1)) 16 s)).1
    have post:=lanes_post h _ bd.1 bd.2 16 (by decide) s mid c (by simpa using here) (check_evaluation_support o _)
    have li:=lanes_inv o heap tree h _ bd.1 bd.2 (by unfold groupBase;omega) 16 (by decide) s c (by simpa using here)
      (by simpa using inv)
    have lt:=latch_post h g le mid post.1 (post.2.trans (congrArg pc (tail_lane h).symm))
    have li' : Inv heap (ctl mid (latch h)) (groupBase h g) := by
      have e : groupBase h (g+1)-16=groupBase h g := by unfold groupBase;omega
      rw [e] at li;exact li.of_mem (latch_mem h mid)
    by_cases g0 : g=0
    · subst g0;rw [groups_zero,eval_pure_fst];exact li'
    · exact ih (by omega) (by omega) _ lt.1 (by rw [lt.2,if_neg g0]) li'

theorem stage_inv (o : Oracle) (heap : Nat → BitVec 238) (tree : ChainedTree o heap) (h : Low)
    (s : MachineState) (lv : Level h s) (inv : Inv heap s (2*count h-1)) :
    Inv heap (checkEvaluation o (stage h s)).1 (count h-1) := by
  have sz:=count_size h
  unfold stage
  rw [eval_bind_fst,eval_pure_fst]
  have start : groupBase h (groupsN h)=2*count h-1 := by unfold groupBase;omega
  have gi:=groups_inv o heap tree h (groupsN h) (groupsN_pos h) le_rfl _ (header_cursor h s lv) (header_pc h s lv.pcAt)
    (by rw [start];exact inv.of_mem (header_mem h s))
  have e : groupBase h 0=count h-1 := by unfold groupBase;omega
  rw [e] at gi;exact gi.of_mem (shift_mem _)

theorem fast_inv (o : Oracle) (heap : Nat → BitVec 238) (tree : ChainedTree o heap) :
    ∀ r, 1≤r → r≤8 → ∀ s, Level (lowAt r) s → Inv heap s (2*count (lowAt r)-1) →
      Inv heap (checkEvaluation o (fast r s)).1 (2^16-1) := by
  intro r
  induction r with
  | zero => intro one;omega
  | succ r ih =>
    intro _ le s lv inv
    rw [fast_succ,eval_bind_fst]
    let mid:=(checkEvaluation o (stage (lowAt (r+1)) s)).1
    have si:=stage_inv o heap tree _ s lv inv
    have a:=stage_post _ s mid lv (check_evaluation_support o _)
    by_cases r0 : r=0
    · subst r0;rw [fast_zero,eval_pure_fst]
      have c7 : count (lowAt 1)=65536 := by decide +kernel
      rw [c7] at si;exact si
    · have lt : (lowAt (r+1)).val<7 := by simp [lowAt];omega
      have nx:=a.next lt
      have cn:=count_next _ lt
      rw [lowAt_next r (by omega) (by omega)] at nx cn
      exact ih (by omega) (by omega) mid nx (by rw [show 2*count (lowAt r)-1=count (lowAt (r+1))-1 by omega];exact si)

theorem phys_eq (s : MachineState) (i : Nat) : phys s i=heapDigest s i := by unfold phys;rfl
theorem logical_eq (heap : Nat → BitVec 238) (i : Nat) : logical heap i=(heap i).setWidth 256 := rfl

theorem inv_init (heap : Nat → BitVec 238) (s : MachineState) (prior : RawLeaves s heap) :
    Inv heap s (2^24-1) := by
  refine ⟨frontier_init view (logical heap) (phys s) (fun i a b=>?_),fun i a b=>by omega⟩
  rw [view,if_pos a,phys_eq,logical_eq];exact prior i a b

theorem inv_handoff (heap : Nat → BitVec 238) (s : MachineState) (inv : Inv heap s (2^16-1)) :
    HeapContent s heap (2^16-1) := by
  constructor;intro i a b
  have f:=inv.front i a b
  by_cases act : i≤2*(2^16-1)+1
  · rw [if_pos act,inv.stable i a (by omega),phys_eq,logical_eq] at f;exact f
  · rw [if_neg act,phys_eq,logical_eq] at f;exact f

/-! Memory above the heap is never written by the specialized heights. -/

theorem sd_x0_getMem (t : MachineState) (r : Reg) (imm : BitVec 12) (a : Word) (h : a≠0#64+signExtend12 imm) :
    (execInstrBr t (.SD .x0 r imm)).getMem a=t.getMem a := by
  show (t.setMem (t.getReg .x0+signExtend12 imm) (t.getReg r)).getMem a=t.getMem a
  exact MachineState.getMem_setMem_ne h

theorem setup_getMem (s : MachineState) (a : Word) (h1 : a≠264) (h2 : a≠272) (h3 : a≠280) :
    (ctl s setup).getMem a=s.getMem a := by
  have e1 : (0#64+signExtend12 (264:BitVec 12))=264 := by decide
  have e2 : (0#64+signExtend12 (272:BitVec 12))=272 := by decide
  have e3 : (0#64+signExtend12 (280:BitVec 12))=280 := by decide
  show (execInstrBr _ (.SD .x0 .x1 280)).getMem a=_
  rw [sd_x0_getMem _ _ _ _ (by rw [e3];exact h3)]
  show (execInstrBr _ (.SD .x0 .x0 272)).getMem a=_
  rw [sd_x0_getMem _ _ _ _ (by rw [e2];exact h2)]
  show (execInstrBr _ (.SD .x0 .x0 264)).getMem a=_
  rw [sd_x0_getMem _ _ _ _ (by rw [e1];exact h1)]
  rfl

def Above (q : Nat) : Prop := heapBase+32*2^25≤q ∧ q%8=0 ∧ q+32≤2^64

theorem above_safe (n q : Nat) (b : Bounds n) (a : Above q) : SafeWord n q := by
  refine ⟨a.2.1,a.2.2,?_⟩;intro i hi;have:=b.upper;have:=a.1;unfold address heapBase at *;split_ifs <;> omega

theorem lanes_mem (h : Low) (G : Nat) (lo : 65536+15≤G) (hi : G<2^24) (q : Nat) (aq : Above q) :
    ∀ r, r≤16 → ∀ s t, t∈support (lanes h G r s) → t.getMem (W q)=s.getMem (W q) := by
  intro r;induction r with
  | zero => intro _ s t ht;rw [show lanes h G 0 s=pure s from rfl,support_pure,Set.mem_singleton_iff] at ht;rw [ht]
  | succ r ih =>
    intro small s t ht
    rw [show lanes h G (r+1) s=(trace (G-(15-r)) (plan h) s >>= lanes h G r) from rfl] at ht
    simp only [mem_support_bind_iff] at ht;obtain ⟨mid,one,rest⟩:=ht
    exact (ih (by omega) mid t rest).trans
      (traceMem _ (lane_bounds ⟨15-r,by omega⟩ lo hi) q (above_safe _ q (lane_bounds ⟨15-r,by omega⟩ lo hi) aq) _ s mid one)

theorem groups_mem (h : Low) (q : Nat) (aq : Above q) :
    ∀ g, g≤groupsN h → ∀ s t, t∈support (groups h g s) → t.getMem (W q)=s.getMem (W q) := by
  intro g;induction g with
  | zero => intro _ s t ht;rw [groups_zero,support_pure,Set.mem_singleton_iff] at ht;rw [ht]
  | succ g ih =>
    intro le s t ht
    have bd:=group_bounds h (g+1) (by omega) le
    rw [groups_succ] at ht;simp only [mem_support_bind_iff] at ht;obtain ⟨mid,one,rest⟩:=ht
    exact ((ih (by omega) _ t rest).trans (getMem_of_mem (latch_mem h mid) _)).trans
      (lanes_mem h _ bd.1 bd.2 q aq 16 (by decide) s mid one)

theorem stage_mem (h : Low) (q : Nat) (aq : Above q) (s t : MachineState) (ht : t∈support (stage h s)) :
    t.getMem (W q)=s.getMem (W q) := by
  simp only [stage,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at ht
  obtain ⟨u,hu,rfl⟩:=ht
  exact ((getMem_of_mem (shift_mem u) _).trans (groups_mem h q aq _ le_rfl _ u hu)).trans
    (getMem_of_mem (header_mem h s) _)

theorem fast_mem (q : Nat) (aq : Above q) : ∀ r s t, t∈support (fast r s) → t.getMem (W q)=s.getMem (W q) := by
  intro r;induction r with
  | zero => intro s t ht;rw [fast_zero,support_pure,Set.mem_singleton_iff] at ht;rw [ht]
  | succ r ih =>
    intro s t ht;rw [fast_succ] at ht;simp only [mem_support_bind_iff] at ht;obtain ⟨mid,one,rest⟩:=ht
    exact (ih mid t rest).trans (stage_mem _ q aq s mid one)

/-! The complete specialized phase. -/

theorem fast_levels_content (o : Oracle) (heap : Nat → BitVec 238) (tree : ChainedTree o heap)
    (s : MachineState) (here : s.pc=pc 45688) (entry : FastEntry s) (output : s.getReg .x8=4294971392)
    (prior : RawLeaves s heap) :
    let a:=(checkEvaluation o (fast 8 (ctl s setup))).1
    let c:=(checkEvaluation o (parentLevels 16 (ctl a handoff))).1
    HeapContent c heap 0 ∧ c.getReg .x9=4294971424 ∧ c.getReg .x8=4294971392 := by
  intro a c
  have lv:=setup_level s here entry output
  have heapWords (i : Nat) (k : Nat) (hi : i<2^25) (hk : k<4) :
      (ctl s setup).getMem (W (heapBase+32*i+8*k))=s.getMem (W (heapBase+32*i+8*k)) := by
    have big : heapBase+32*i+8*k<2^64 := by unfold heapBase;omega
    have low : 280<heapBase+32*i+8*k := by unfold heapBase;omega
    apply setup_getMem <;> intro e
    · have n:=congrArg BitVec.toNat (e.trans (show (264:Word)=W 264 from rfl))
      simp only [W,BitVec.toNat_ofNat] at n;omega
    · have n:=congrArg BitVec.toNat (e.trans (show (272:Word)=W 272 from rfl))
      simp only [W,BitVec.toNat_ofNat] at n;omega
    · have n:=congrArg BitVec.toNat (e.trans (show (280:Word)=W 280 from rfl))
      simp only [W,BitVec.toNat_ofNat] at n;omega
  have p0 (i : Nat) (hi : i<2^25) : phys (ctl s setup) i=phys s i := by
    unfold phys heapDigest
    exact read_digest_congr _ _ _ (by unfold heapBase;omega) (fun k hk=>heapWords i k hi hk)
  have inv0 : Inv heap (ctl s setup) (2^24-1) := by
    have i0:=inv_init heap s prior
    exact ⟨fun i x y=>by rw [p0 i y];exact i0.front i x y,fun i x y=>by rw [p0 i (by omega)];exact i0.stable i x y⟩
  have c8 : 2*count (lowAt 8)-1=2^24-1 := by decide +kernel
  have fi:=fast_inv o heap tree 8 (by decide) le_rfl _ lv (by rw [c8];exact inv0)
  have fin:=fast_post 8 (by decide) le_rfl _ a lv (check_evaluation_support o _)
  have hc0:=inv_handoff heap a fi
  have hcb : HeapContent (ctl a handoff) heap (2*heightCount (heightAt 16)-1) := by
    rw [show 2*heightCount (heightAt 16)-1=2^16-1 by decide +kernel];exact hc0.frame (getMem_of_mem (handoff_mem a))
  have ready:=handoff_ready a fin
  have reached:=check_evaluation_support o (parentLevels 16 (ctl a handoff))
  refine ⟨parent_levels_content o heap tree 16 (by decide) (by decide) _ ready hcb,?_,?_⟩
  · exact (parent_levels_register 16 _ c reached .x9 (by simp [ParentSaved])).trans
      ((handoff_reg a .x9 (by decide) (by decide)).trans fin.heap)
  · exact (parent_levels_register 16 _ c reached .x8 (by simp [ParentSaved])).trans
      ((handoff_reg a .x8 (by decide) (by decide)).trans fin.output)

theorem fast_parent_eval (o : Oracle) (s : MachineState) :
    (checkEvaluation o (fastParentTrace s)).1=chainedRootPrefix (checkEvaluation o (parentLevels 16
      (ctl (checkEvaluation o (fast 8 (ctl s setup))).1 handoff))).1 10 := by
  unfold fastParentTrace;rw [eval_bind_fst,eval_bind_fst,eval_pure_fst]

theorem fast_part_memory (o : Oracle) (s : MachineState) (q : Nat) (aq : Above q) :
    (ctl (checkEvaluation o (fast 8 (ctl s setup))).1 handoff).getMem (W q)=s.getMem (W q) := by
  have a:=aq.1
  rw [getMem_of_mem (handoff_mem _),fast_mem q aq 8 _ _ (check_evaluation_support o _)]
  have room:=aq.2.2
  unfold heapBase at a
  apply setup_getMem <;> intro e
  · have n:=congrArg BitVec.toNat (e.trans (show (264:Word)=W 264 from rfl))
    simp only [W,BitVec.toNat_ofNat] at n;omega
  · have n:=congrArg BitVec.toNat (e.trans (show (272:Word)=W 272 from rfl))
    simp only [W,BitVec.toNat_ofNat] at n;omega
  · have n:=congrArg BitVec.toNat (e.trans (show (280:Word)=W 280 from rfl))
    simp only [W,BitVec.toNat_ofNat] at n;omega

theorem fast_part_ready (o : Oracle) (s : MachineState) (here : s.pc=pc 45688) (entry : FastEntry s)
    (output : s.getReg .x8=4294971392) :
    HeapLevelReady (ctl (checkEvaluation o (fast 8 (ctl s setup))).1 handoff) (heightAt 16) (heightCount (heightAt 16)) ∧
    (ctl (checkEvaluation o (fast 8 (ctl s setup))).1 handoff).getReg .x8=4294971392 := by
  have lv:=setup_level s here entry output
  have fin:=fast_post 8 (by decide) le_rfl _ _ lv (check_evaluation_support o _)
  exact ⟨handoff_ready _ fin,(handoff_reg _ .x8 (by decide) (by decide)).trans fin.output⟩

end CommitGolfCandidate.Chained.Native.Fast
