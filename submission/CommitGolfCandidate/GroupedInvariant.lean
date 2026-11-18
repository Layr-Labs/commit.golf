import CommitGolfCandidate.GroupedFrame
import CommitGolfCandidate.GroupedScan
import CommitGolfCandidate.LinkedSaltLayout
import CommitGolfCandidate.K3CBDefs

/-!
# The K3-lite body invariant

`Good … regs m n` describes registers and memory before slot `n`, in two parts.

* `MsgGood` (message area and key block): later messages intact (the C message of a pending pair
  excepted), key block intact, the group's generator reply at `genWord n` (ranks ≥ 1), the pending
  C leaf's first reply tail and message tail (rank 1), x14..x17 = generator words 16..19 (ranks 9,
  10), and, before a linked head, the previous head's generator reply at `msgWord n - 336` (the
  linked generator call reads it in place).
* `CellGood` (quartet blocks): the digests of all earlier leaves at `qLeaf`, except the fourth leaf
  of an even quartet (its digest is overwritten by the group reply `reply_E`); the group reply of
  every finished quartet at `replyWord g`; the 72 zero bytes at the head of every block.

The generator replies follow the final salt schedule `chain` (a keyed restart every 34 heads of a
tile, every other head linked to the previous head's reply).
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate.Permutation.CounterSalt (coord input parts)
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000

structure MsgGood (o : Oracle) (k : BitVec 192) (msg : Message) (regs : Reg → Word) (m : Memory) (n : Nat) : Prop where
  messages : ∀ i : Index, n ≤ i.val → (rank n=1 → n≠i.val) → window m (msgWord i.val)=messageWords msg i
  key : KeyIntact m k
  group : ∀ i : Index, n=i.val → rank n≠0 → window m (genWord n)=replyWords (groupReply o k i)
  pending : ∀ i : Index, n=i.val → rank n=1 →
    (∀ j : Fin 11, m (msgWord n+10+j.val)=replyWords (firstOf o msg i) ⟨14+j.val,by omega⟩) ∧
    (∀ j : Fin 11, m (msgWord n+21+j.val)=messageWords msg i ⟨21+j.val,by omega⟩)
  prefetched : ∀ i : Index, n=i.val → 9 ≤ rank n →
    regs .x14=replyWords (groupReply o k i) ⟨16,by omega⟩ ∧ regs .x15=replyWords (groupReply o k i) ⟨17,by omega⟩ ∧
    regs .x16=replyWords (groupReply o k i) ⟨18,by omega⟩ ∧ regs .x17=replyWords (groupReply o k i) ⟨19,by omega⟩
  previous : ∀ i j : Index, n=i.val → j.val+11=n → rank n=0 → n%4096/11%34≠0 →
    window m (genWord (n-11))=replyWords (groupReply o k j)

structure CellGood (o : Oracle) (k : BitVec 192) (msg : Message) (m : Memory) (n : Nat) : Prop where
  children : ∀ i : Index, i.val<n → ¬(i.val%4=3 ∧ i.val/4%2=0) → window m (qLeaf i.val)=digestOf (value o k msg i)
  replies : ∀ g, 4*g+4≤n → window m (replyWord g)=replyWords (quartetReply o k msg g)
  padding : ∀ g<4194304, ∀ j<9, m (qSource g+j)=0

structure Good (o : Oracle) (k : BitVec 192) (msg : Message) (regs : Reg → Word) (m : Memory) (n : Nat) : Prop where
  msgs : MsgGood o k msg regs m n
  cells : CellGood o k msg m n

theorem next_coord (i j : Index) (step : j.val=i.val+1) (active : rank j.val≠0) : (coord j).1=(coord i).1 := by
  have edge : i.val%4096≠4095 := by intro h;apply active;unfold rank;rw [step,show (i.val+1)%4096=0 by omega]
  have a : j.val/4096=i.val/4096 := by omega
  have b : j.val%4096=i.val%4096+1 := by omega
  have c : j.val%4096/11=i.val%4096/11 := by unfold rank at active;rw [b] at active ⊢;omega
  apply Fin.ext;simp only [coord,a,c]

theorem next_genWord (i : Nat) (active : rank (i+1)≠0) : genWord (i+1)=genWord i := by
  have r := rank_next i active
  have : rank i ≤ i := by unfold rank;omega
  unfold genWord;rw [r,show i+1-(rank i+1)=i-rank i by omega]

theorem salt_slice (o : Oracle) (k : BitVec 192) (i : Index) :
    saltWords (chainSalts o k i)=Counter.slice (replyWords (groupReply o k i)) (coord i).2 := by
  exact (Counter.slice_eq _ _).symm

theorem coord_rank (i : Index) : (coord i).2=⟨rank i.val,rank_lt i.val⟩ := rfl

/-- The head index of the group of `i` inside its tile (`(coord i).1 mod 373`). -/
theorem coord_mod (i : Index) : (coord i).1.val%373=i.val%4096/11 := by
  unfold coord;dsimp only;omega

/-- The head before the head `i` (same tile) is `i - 11`. -/
theorem pred_coord (i j : Index) (step : j.val+11=i.val) (inner : i.val%4096/11≠0) :
    CommitGolfCandidate.Permutation.LinkedSalt.pred (coord i).1=(coord j).1 := by
  have big : 11 ≤ i.val%4096 := by
    rcases Nat.lt_or_ge (i.val%4096) 11 with h|h
    · exfalso;apply inner;rw [Nat.div_eq_of_lt h]
    · exact h
  apply Fin.ext
  simp only [CommitGolfCandidate.Permutation.LinkedSalt.pred,coord]
  have d := Nat.div_add_mod i.val 4096
  have a : j.val/4096=i.val/4096 := by clear inner;omega
  have b : j.val%4096=i.val%4096-11 := by clear inner;omega
  rw [a,b]
  have hm : i.val%4096<4096 := Nat.mod_lt _ (by decide)
  generalize i.val%4096=x at *
  clear inner a b d
  omega

theorem value_eq (o : Oracle) (k : BitVec 192) (msg : Message) (i : Index) :
    value o k msg i=outputDigest (o.permutation (packBuffer (pinnedSecondInput i (saltWords (chainSalts o k i))
      (replyWords (firstOf o msg i)) (messageWords msg i)))) := rfl

theorem digest_from_window (o : Oracle) (k : BitVec 192) (msg : Message) (M : Memory) (i : Index) (a : Nat)
    (win : window M a=pinnedSecondInput i (saltWords (chainSalts o k i)) (replyWords (firstOf o msg i))
      (messageWords msg i)) :
    lowDigest (replyWords (callReply o M a))=digestOf (value o k msg i) := by
  funext j
  have r : callReply o M a=o.permutation (packBuffer (pinnedSecondInput i (saltWords (chainSalts o k i))
      (replyWords (firstOf o msg i)) (messageWords msg i))) := by unfold callReply;rw [win]
  rw [r]
  exact (low_digest_word _ j).trans
    (congrArg (fun d : BitVec 256 => d.extractLsb' (64*j.val) 64) (value_eq o k msg i).symm)

theorem first_window (o : Oracle) (msg : Message) (m : Memory) (i : Index)
    (msgEq : window m (msgWord i.val)=messageWords msg i) :
    callReply o m (if rank i.val=0 then msgWord i.val+7 else msgWord i.val)=firstOf o msg i := by
  have w (d : Nat) (hd : d<32) : m (msgWord i.val+d)=messageWords msg i ⟨d,hd⟩ := congrFun msgEq ⟨d,hd⟩
  have e : (window m (if rank i.val=0 then msgWord i.val+7 else msgWord i.val) : Words 25)=
      pinnedFirstInput i (messageWords msg i) := by
    funext j
    by_cases h : rank i.val=0
    · simp only [pinnedFirstInput,window,h,ahead_true i h,↓reduceIte]
      exact (congrArg m (by omega : msgWord i.val+7+j.val=msgWord i.val+(j.val+7))).trans (w _ (by omega))
    · simp only [pinnedFirstInput,window,h,ahead_false i h,Bool.false_eq_true,↓reduceIte]
      exact w _ (by omega)
  calc callReply o m (if rank i.val=0 then msgWord i.val+7 else msgWord i.val)
      =o.permutation (packBuffer (pinnedFirstInput i (messageWords msg i))) := by unfold callReply;rw [e]
    _=firstOf o msg i := rfl

private theorem bounds (i : Nat) (hi : i<16777216) :
    512≤msgWord i ∧ msgWord i+64<qSalt 0 ∧ msgWord i+64<qSource 0 := by
  unfold msgWord qSalt qSource;omega

/-- The generator reply a head computes: keyed (key block with its counter) or linked (the previous
head's reply read in place); both equal the schedule's reply for the group. -/
theorem head_generated (o : Oracle) (k : BitVec 192) (msg : Message) (regs : Reg → Word) (m : Memory) (i : Index)
    (h : MsgGood o k msg regs m i.val) (r0 : rank i.val=0) :
    generated o m i.val=groupReply o k i := by
  have hi : i.val<16777216 := i.isLt
  by_cases kd : i.val%4096/11%34=0
  · exact (generated_eq o m i k h.key r0 kd).trans
      (CommitGolfCandidate.Permutation.LinkedSalt.reply_keyed CommitGolfCandidate.Permutation.LinkedSalt.period
        o.permutation k (coord i).1 (by rw [coord_mod];exact kd)).symm
  · have big : 11 ≤ i.val := Nat.le_trans (linked_big i.val kd) (Nat.mod_le _ _)
    have jb : i.val-11<16777216 := by omega
    let j : Index := ⟨i.val-11,jb⟩
    have step : j.val+11=i.val := Nat.sub_add_cancel big
    have prev := h.previous i j rfl step r0 kd
    have e := CommitGolfCandidate.Permutation.LinkedSalt.reply_linked CommitGolfCandidate.Permutation.LinkedSalt.period
      o.permutation k (coord i).1 (by rw [coord_mod];exact kd)
    rw [pred_coord i j step (by intro z;rw [z] at kd;exact kd (by decide))] at e
    exact (generated_linked o m i.val (groupReply o k j) hi r0 kd prev).trans e.symm

/-- The key block after a slot (only word 0, the counter, may change). -/
theorem key_step (o : Oracle) (k : BitVec 192) (regs : Reg → Word) (m : Memory) (i : Index)
    (key : KeyIntact m k) : KeyIntact (c2Mem o regs m i.val) k := by
  have hi : i.val<16777216:=i.isLt
  obtain ⟨b1,b2,b3⟩ := bounds i.val hi
  intro j lo up
  apply Eq.trans _ (key j lo up)
  apply packet_frame o regs m i.val _ hi <;> simp only [qSalt,qLeaf,qSource] at * <;> omega

theorem msg_head (o : Oracle) (k : BitVec 192) (msg : Message) (v : View) (i : Index)
    (h : MsgGood o k msg v.regs v.mem i.val) (r0 : rank i.val=0) :
    lowDigest (replyWords (digestReply o v.regs v.mem i.val))=digestOf (value o k msg i) ∧
    MsgGood o k msg ((plan i.val).foldl (viewStep o) v).regs (c2Mem o v.regs v.mem i.val) (i.val+1) := by
  have hi : i.val<16777216:=i.isLt
  obtain ⟨b1,b2,b3⟩ := bounds i.val hi
  have c1 := head_pair i.val r0
  have nlt : i.val+1<16777216 := by unfold rank at r0 c1;omega
  obtain ⟨c,hc⟩ : ∃ c : Index, c.val=i.val+1 := ⟨⟨i.val+1,nlt⟩,rfl⟩
  have msgI := h.messages i le_rfl (by omega)
  have msgC := h.messages c (by omega) (by omega)
  have cw : msgWord (i.val+1)=msgWord i.val+32 := by unfold msgWord;omega
  have sec : secondWord i.val=msgWord i.val-7 := by unfold secondWord;rw [if_pos r0]
  have win := head_second_window o v.mem i r0
  have gen := head_generated o k msg v.regs v.mem i h r0
  have fst := first_window o msg v.mem i msgI
  rw [if_pos r0] at fst
  have dig : lowDigest (replyWords (digestReply o v.regs v.mem i.val))=digestOf (value o k msg i) := by
    unfold digestReply preSecond;rw [if_pos r0,sec]
    apply digest_from_window
    rw [win,gen,fst,msgI,salt_slice,coord_rank]
    congr 2;exact Fin.ext r0.symm
  refine ⟨dig,?_⟩
  have grp : groupReply o k c=groupReply o k i := by
    unfold groupReply;rw [next_coord i c hc (by rw [hc];omega)]
  constructor
  · intro j lo ex
    have j2 : i.val+2≤j.val := by
      by_cases e : i.val+1=j.val
      · exact absurd e (ex c1)
      · omega
    apply Eq.trans _ (h.messages j (by omega) (by omega));funext a
    have t:=a.isLt;have ix : j.val<16777216:=j.isLt
    apply packet_frame _ _ _ _ _ hi <;> simp only [msgWord,qSalt,qLeaf,qSource] at * <;> omega
  · exact key_step o k v.regs v.mem i h.key
  · intro j eq _
    have ej : j=c := Fin.ext (by omega)
    rw [ej]
    have gw : genWord (i.val+1)=msgWord i.val+16 := by
      unfold genWord;rw [c1,show i.val+1-1=i.val by omega]
    rw [gw,head_generator _ _ _ _ hi r0,gen,grp]
  · intro j eq _
    have ej : j=c := Fin.ext (by omega)
    rw [ej]
    constructor
    · intro t
      rw [cw,show msgWord i.val+32+10+t.val=msgWord i.val+42+t.val by omega,head_c_reply _ _ _ _ hi r0 t,c_first_eq]
      have fc := first_window o msg v.mem c msgC
      rw [hc,if_neg (show ¬rank (i.val+1)=0 by omega),cw] at fc
      unfold callReply at fc;rw [fc]
    · intro t
      have tt := t.isLt
      rw [cw,show msgWord i.val+32+21+t.val=msgWord i.val+53+t.val by omega,
        head_c_tail o v.regs v.mem i.val hi r0 (msgWord i.val+53+t.val) (by omega) (by omega)]
      have e := congrFun msgC ⟨21+t.val,by omega⟩
      simp only [window] at e
      rw [hc,cw] at e
      rw [←e];congr 1;omega
  · intro j eq rk
    rw [c1] at rk;omega
  · intro _ _ _ _ rk
    rw [c1] at rk;omega

theorem msg_c (o : Oracle) (k : BitVec 192) (msg : Message) (v : View) (i : Index)
    (h : MsgGood o k msg v.regs v.mem i.val) (r1 : rank i.val=1) (x10 : v.regs .x10=wordAddress (entryWord i.val)) :
    lowDigest (replyWords (digestReply o v.regs v.mem i.val))=digestOf (value o k msg i) ∧
    MsgGood o k msg ((plan i.val).foldl (viewStep o) v).regs (c2Mem o v.regs v.mem i.val) (i.val+1) := by
  have hi : i.val<16777216:=i.isLt
  obtain ⟨b1,b2,b3⟩ := bounds i.val hi
  have r0 : rank i.val≠0 := by omega
  have grpI := h.group i rfl r0
  obtain ⟨pr,pt⟩ := h.pending i rfl r1
  have gw : genWord i.val+23=msgWord i.val+7 := by have := genWord_rank i.val 1 r1;omega
  have saltW : (window v.mem (msgWord i.val+7) : Words 2)=saltWords (chainSalts o k i) := by
    have sw := Counter.slice_window _ ⟨1,by decide⟩ _ _ grpI
    rw [show Counter.sliceStart ⟨1,by decide⟩=23 by decide,gw] at sw
    rw [sw,salt_slice,coord_rank]
    congr 1;exact Fin.ext r1.symm
  have sec : secondWord i.val=msgWord i.val+7 := by unfold secondWord;rw [if_neg r0]
  have dig : lowDigest (replyWords (digestReply o v.regs v.mem i.val))=digestOf (value o k msg i) := by
    unfold digestReply preSecond;rw [if_neg r0,if_pos r1,sec]
    apply digest_from_window
    have tag : v.regs .x10=wordAddress (msgWord i.val+7) := by
      rw [x10];unfold entryWord;rw [if_pos (by omega)]
    exact c_second_window v.regs v.mem i r0 tag _ _ _ saltW pr pt
  refine ⟨dig,?_⟩
  have n2 : rank (i.val+1)=2 := by
    have := rank_next i.val (by unfold rank at r1 ⊢;omega);omega
  constructor
  · intro j lo _
    apply Eq.trans _ (h.messages j (by omega) (by intro _ e;rw [←e] at lo;omega));funext a
    have t:=a.isLt;have ix : j.val<16777216:=j.isLt
    apply c_frame _ _ _ _ _ r1 <;> simp only [msgWord,qSalt,qLeaf,qSource] at * <;> omega
  · exact key_step o k v.regs v.mem i h.key
  · intro j eq _
    have gn := next_genWord i.val (by omega)
    have g1 := genWord_rank i.val 1 r1
    have grp : groupReply o k j=groupReply o k i := by
      unfold groupReply;rw [next_coord i j eq.symm (by rw [←eq];omega)]
    rw [gn,grp,←grpI];funext a
    have t:=a.isLt
    apply c_frame _ _ _ _ _ r1
    · omega
    · unfold qLeaf qSource;unfold msgWord at g1;omega
  · intro j eq rk;omega
  · intro j eq rk;omega
  · intro _ _ _ _ rk;omega

theorem msg_follower (o : Oracle) (k : BitVec 192) (msg : Message) (v : View) (i : Index)
    (h : MsgGood o k msg v.regs v.mem i.val) (r0 : rank i.val≠0) (r1 : rank i.val≠1) :
    lowDigest (replyWords (digestReply o v.regs v.mem i.val))=digestOf (value o k msg i) ∧
    MsgGood o k msg ((plan i.val).foldl (viewStep o) v).regs (c2Mem o v.regs v.mem i.val) (i.val+1) := by
  have hi : i.val<16777216:=i.isLt
  obtain ⟨b1,b2,b3⟩ := bounds i.val hi
  have rl := rank_lt i.val
  have grpI := h.group i rfl r0
  have msgI := h.messages i le_rfl (by omega)
  have g := genWord_rank i.val (rank i.val) rfl
  have gen (t : Nat) (ht : t<25) : v.mem (genWord i.val+t)=replyWords (groupReply o k i) ⟨t,ht⟩ :=
    congrFun grpI ⟨t,ht⟩
  have saltEq : followerSalt v.regs v.mem i.val=saltWords (chainSalts o k i) := by
    rw [salt_slice,coord_rank];funext d
    have hd := d.isLt
    unfold followerSalt Counter.slice Counter.sliceStart
    simp only [Fin.val_mk,r0,r1,ite_false]
    split
    · unfold sourceWord;rw [Nat.add_assoc,gen (2*(rank i.val-1)+d.val) (by omega)]
    split
    · obtain ⟨p14,p15,_,_⟩ := h.prefetched i rfl (by omega)
      split
      · rw [p14];congr 1;apply Fin.ext;simp only [Fin.val_mk];omega
      · rw [p15];congr 1;apply Fin.ext;simp only [Fin.val_mk];omega
    · obtain ⟨_,_,p16,p17⟩ := h.prefetched i rfl (by omega)
      split
      · rw [p16];congr 1;apply Fin.ext;simp only [Fin.val_mk];omega
      · rw [p17];congr 1;apply Fin.ext;simp only [Fin.val_mk];omega
  have sec : secondWord i.val=msgWord i.val+7 := by unfold secondWord;rw [if_neg r0]
  have fst := first_window o msg v.mem i msgI
  rw [if_neg r0] at fst
  have dig : lowDigest (replyWords (digestReply o v.regs v.mem i.val))=digestOf (value o k msg i) := by
    unfold digestReply preSecond;rw [if_neg r0,if_neg r1,sec]
    apply digest_from_window
    rw [follower_second_window o v.regs v.mem i r0 r1,saltEq,fst,msgI]
  refine ⟨dig,?_⟩
  have keepLow (a : Nat) (ha : a<msgWord i.val-4) : c2Mem o v.regs v.mem i.val a=v.mem a :=
    follower_frame _ _ _ _ _ hi r0 (Or.inl ha) (Or.inl (by simp only [qLeaf,qSource] at b3 ⊢;omega))
  have pf := plan_prefetch o v i.val
  constructor
  · intro j lo _
    apply Eq.trans _ (h.messages j (by omega) (by omega));funext a
    have t:=a.isLt;have ix : j.val<16777216:=j.isLt
    apply follower_frame _ _ _ _ _ hi r0 <;> simp only [msgWord,qSalt,qLeaf,qSource] at * <;> omega
  · exact key_step o k v.regs v.mem i h.key
  · intro j eq act
    have gn := next_genWord i.val (by omega)
    have grp : groupReply o k j=groupReply o k i := by
      unfold groupReply;rw [next_coord i j eq.symm (by rw [←eq];omega)]
    rw [gn,grp,←grpI];funext a
    have t:=a.isLt
    exact keepLow _ (by omega)
  · intro j eq rk
    have ne : rank (i.val+1)≠0 := by omega
    have rn := rank_next i.val ne
    omega
  · intro j eq rk
    have ne : rank (i.val+1)≠0 := by omega
    have rn := rank_next i.val ne
    have grp : groupReply o k j=groupReply o k i := by
      unfold groupReply;rw [next_coord i j eq.symm (by rw [←eq];omega)]
    rw [grp]
    by_cases e8 : rank i.val=8
    · obtain ⟨p14,p15,p16,p17⟩ := pf.1 e8
      have at16 (t : Nat) (ht : t<4) : preSecond o v.regs v.mem i.val (genWord i.val+16+t)=
          replyWords (groupReply o k i) ⟨16+t,by omega⟩ := by
        have gs : genWord i.val+25≤msgWord i.val := by omega
        rw [pre_packet o v.regs v.mem i.val (genWord i.val+16+t)
            (Or.inl (by simp only [qLeaf,qSource] at b3 ⊢;omega)),
          keepLow (genWord i.val+16+t) (by omega),Nat.add_assoc,gen (16+t) (by omega)]
      refine ⟨p14.trans (at16 0 (by decide)),p15.trans ?_,p16.trans ?_,p17.trans ?_⟩
      · exact at16 1 (by decide)
      · exact at16 2 (by decide)
      · exact at16 3 (by decide)
    · obtain ⟨p14,p15,p16,p17⟩ := pf.2 e8
      obtain ⟨q14,q15,q16,q17⟩ := h.prefetched i rfl (by omega)
      exact ⟨p14.trans q14,p15.trans q15,p16.trans q16,p17.trans q17⟩
  · intro c j eq step rk linked
    -- the next leaf is a linked head: slot `i` is the rank-10 leaf of the previous group
    have nz : (i.val+1)%4096≠0 := by intro z;rw [z] at linked;exact linked (by decide)
    clear linked
    have r10 : rank i.val=10 := by
      have nw : i.val%4096≠4095 := by intro e;apply nz;omega
      unfold rank at rk ⊢
      rw [show (i.val+1)%4096=i.val%4096+1 by omega] at rk
      omega
    have grp : groupReply o k j=groupReply o k i := by
      unfold groupReply;congr 1;apply Fin.ext;simp only [coord];unfold rank at r10;omega
    have gw : genWord (i.val+1-11)=genWord i.val := by
      have big : 10 ≤ i.val%4096 := by unfold rank at r10;omega
      have st : i.val+1-11=i.val-10 := by omega
      have e : (i.val-10)%4096=i.val%4096-10 := by omega
      have r0' : rank (i.val+1-11)=0 := by
        unfold rank at r10 ⊢;rw [st,e];omega
      unfold genWord;rw [r0',r10,st,Nat.sub_zero]
    rw [gw,grp,←grpI];funext a
    have t:=a.isLt
    exact keepLow _ (by omega)

/-! ## The quartet blocks -/

theorem tail_frame (o : Oracle) (regs : Reg → Word) (m : Memory) (i a : Nat) (hi : i<16777216)
    (out : a<qSource 0 ∨ qSalt 0≤a) : packetMem o regs m i a=c2Mem o regs m i a := by
  unfold packetMem;split
  · apply window_outside
    unfold replyWord;split <;> (unfold qSource qSalt at *;omega)
  · rfl

/-- The message-area facts only read words outside the quartet blocks. -/
theorem msg_congr (o : Oracle) (k : BitVec 192) (msg : Message) (regs : Reg → Word) (m m' : Memory) (n : Nat)
    (eq : ∀ w, (w<qSource 0 ∨ qSalt 0≤w) → w<2^33 → m' w=m w) (bound : n≤16777216) (h : MsgGood o k msg regs m n) :
    MsgGood o k msg regs m' n := by
  constructor
  · intro i hi ex;apply Eq.trans _ (h.messages i hi ex);funext j
    apply eq <;> (have := j.isLt;have ix : i.val<16777216:=i.isLt;unfold msgWord;(try unfold qSource);omega)
  · intro j hj hi;exact (eq _ (by right;unfold qSalt;omega) (by unfold qSalt;omega)).trans (h.key j hj hi)
  · intro i hi a;apply Eq.trans _ (h.group i hi a);funext v
    apply eq <;> (have:=v.isLt;have ix : i.val<16777216:=i.isLt;unfold genWord msgWord;(try unfold qSource);omega)
  · intro i hi a
    obtain ⟨p1,p2⟩ := h.pending i hi a
    have ix : i.val<16777216:=i.isLt
    exact ⟨fun j => (eq _ (by left;have:=j.isLt;unfold msgWord qSource;omega) (by have:=j.isLt;unfold msgWord;omega)).trans (p1 j),
      fun j => (eq _ (by left;have:=j.isLt;unfold msgWord qSource;omega) (by have:=j.isLt;unfold msgWord;omega)).trans (p2 j)⟩
  · exact h.prefetched
  · intro i j hi hj r l;apply Eq.trans _ (h.previous i j hi hj r l);funext v
    apply eq <;> (have:=v.isLt;have ix : i.val<16777216:=i.isLt;unfold genWord msgWord;(try unfold qSource);omega)

theorem leaf_val (o : Oracle) (k : BitVec 192) (msg : Message) (j : Index) : leafVal o k msg j.val=value o k msg j := by
  unfold leafVal;rw [dif_pos j.isLt]

/-- The cell part of a slot: the new digest, the group call of a fourth quartet leaf, and nothing else. -/
theorem cells_step (o : Oracle) (k : BitVec 192) (msg : Message) (regs : Reg → Word) (m : Memory) (i : Index)
    (h : CellGood o k msg m i.val)
    (dig : lowDigest (replyWords (digestReply o regs m i.val))=digestOf (value o k msg i)) :
    CellGood o k msg (packetMem o regs m i.val) (i.val+1) := by
  have hi : i.val<16777216 := i.isLt
  have keep (a : Nat) (lo : qSource 0≤a) (up : a<qSalt 0) (dst : a<qLeaf i.val ∨ qLeaf i.val+25≤a) :
      c2Mem o regs m i.val a=m a :=
    packet_frame o regs m i.val a hi (by unfold qSalt at up ⊢;omega)
      (Or.inr (by unfold qSource at lo;unfold msgWord;omega)) dst
  have newd : window (c2Mem o regs m i.val) (qLeaf i.val)=digestOf (value o k msg i) := (new_digest ..).trans dig
  have tailKeep (a : Nat) (c : i.val%4≠3 ∨ a<replyWord (i.val/4) ∨ replyWord (i.val/4)+25≤a) :
      packetMem o regs m i.val a=c2Mem o regs m i.val a := by
    unfold packetMem;split
    · rename_i t;apply window_outside;omega
    · rfl
  have ql : qLeaf i.val=qSource (i.val/4)+9+4*(i.val%4) := rfl
  refine ⟨?_,?_,?_⟩
  · intro j lo ex
    have hj := j.isLt
    funext t;have ht := t.isLt
    show packetMem o regs m i.val (qLeaf j.val+t.val)=_
    by_cases e : j.val=i.val
    · have ji : j=i := Fin.ext e
      subst ji
      rw [tailKeep _ ?_]
      · exact congrFun newd t
      · by_cases t3 : j.val%4=3
        · have od : j.val/4%2=1 := by omega
          right;right;unfold replyWord;rw [if_neg (by omega)];unfold qLeaf qSource;omega
        · left;exact t3
    · have jl : j.val < i.val := by omega
      have jq : qLeaf j.val+4≤qLeaf i.val := by unfold qLeaf qSource;omega
      rw [tailKeep _ ?_,keep _ (by unfold qLeaf qSource;omega) (by unfold qLeaf qSource qSalt;omega) (Or.inl (by omega))]
      · exact congrFun (h.children j jl ex) t
      · by_cases t3 : i.val%4=3
        · right
          unfold replyWord;split
          · left;rw [show qSource (i.val/4)+21=qLeaf i.val by rw [ql,t3]];omega
          · unfold qLeaf qSource at *;omega
        · left;exact t3
  · intro g hg
    by_cases old : 4*g+4 ≤ i.val
    · funext t;have ht := t.isLt
      show packetMem o regs m i.val (replyWord g+t.val)=_
      have far : replyWord g+25≤qLeaf i.val := by
        unfold replyWord qLeaf qSource;split <;> omega
      rw [tailKeep _ ?_,keep _ (by unfold replyWord qSource;split <;> omega) (by unfold replyWord qSource qSalt;split <;> omega)
        (Or.inl (by omega))]
      · exact congrFun (h.replies g old) t
      · by_cases t3 : i.val%4=3
        · right
          unfold replyWord;split <;> split <;> (unfold qSource;omega)
        · left;exact t3
    · have t3 : i.val%4=3 := by omega
      have eg : g=i.val/4 := by omega
      subst eg
      have win : window (c2Mem o regs m i.val) (qSource (i.val/4))=quartetWindow o k msg (i.val/4) := by
        funext w
        have hw := w.isLt
        show c2Mem o regs m i.val (qSource (i.val/4)+w.val)=_
        unfold quartetWindow
        by_cases z : w.val<9
        · rw [if_pos z,keep _ (by unfold qSource;omega) (by unfold qSource qSalt;omega) (Or.inl (by rw [ql];omega))]
          exact h.padding _ (by omega) _ z
        · rw [if_neg z]
          have kk : (w.val-9)/4<4 := by omega
          have jb : 4*(i.val/4)+(w.val-9)/4<16777216 := by omega
          let j : Index := ⟨4*(i.val/4)+(w.val-9)/4,jb⟩
          have addr : qSource (i.val/4)+w.val=qLeaf j.val+(w.val-9)%4 := by
            simp only [j];unfold qLeaf;rw [show (4*(i.val/4)+(w.val-9)/4)/4=i.val/4 by omega,
              show (4*(i.val/4)+(w.val-9)/4)%4=(w.val-9)/4 by omega];omega
          rw [addr,show 4*(i.val/4)+(w.val-9)/4=j.val from rfl,leaf_val]
          by_cases last : (w.val-9)/4=3
          · have ji : j=i := Fin.ext (by simp only [j];omega)
            rw [ji];exact congrFun newd ⟨(w.val-9)%4,by omega⟩
          · have jl : j.val < i.val := by simp only [j];omega
            rw [keep _ (by unfold qLeaf qSource;omega) (by unfold qLeaf qSource qSalt;omega)
              (Or.inl (by unfold qLeaf qSource;simp only [j];omega))]
            exact congrFun (h.children j jl (by simp only [j];omega)) ⟨(w.val-9)%4,by omega⟩
      have tr : tailReply o regs m i.val=quartetReply o k msg (i.val/4) := by
        unfold tailReply callReply quartetReply;rw [win]
      funext t;have ht := t.isLt
      show packetMem o regs m i.val (replyWord (i.val/4)+t.val)=_
      unfold packetMem;rw [if_pos t3,ww_in _ _ _ _ (by omega) (by omega),tr]
      congr 1;apply Fin.ext;simp only [Fin.val_mk];omega
  · intro g hg j hj
    rw [tailKeep _ ?_,keep _ (by unfold qSource;omega) (by unfold qSource qSalt;omega)
      (by rw [ql];unfold qSource;omega)]
    · exact h.padding g hg j hj
    · by_cases t3 : i.val%4=3
      · right;unfold replyWord;split <;> (unfold qSource;omega)
      · left;exact t3

theorem good_step (o : Oracle) (k : BitVec 192) (msg : Message) (v : View) (i : Index)
    (h : Good o k msg v.regs v.mem i.val) (x10 : v.regs .x10=wordAddress (entryWord i.val)) :
    Good o k msg ((plan i.val).foldl (viewStep o) v).regs ((plan i.val).foldl (viewStep o) v).mem (i.val+1) := by
  rw [plan_meaning]
  have hi : i.val<16777216 := i.isLt
  obtain ⟨dig,mg⟩ : lowDigest (replyWords (digestReply o v.regs v.mem i.val))=digestOf (value o k msg i) ∧
      MsgGood o k msg ((plan i.val).foldl (viewStep o) v).regs (c2Mem o v.regs v.mem i.val) (i.val+1) := by
    by_cases r0 : rank i.val=0
    · exact msg_head o k msg v i h.msgs r0
    by_cases r1 : rank i.val=1
    · exact msg_c o k msg v i h.msgs r1 x10
    exact msg_follower o k msg v i h.msgs r0 r1
  exact ⟨msg_congr o k msg _ _ _ _ (fun w out _ => tail_frame o v.regs v.mem i.val w hi out) (by omega) mg,
    cells_step o k msg v.regs v.mem i h.cells dig⟩

theorem good_congr (o : Oracle) (k : BitVec 192) (msg : Message) (regs regs' : Reg → Word) (m m' : Memory) (n : Nat)
    (er : ∀ r, regs' r=regs r) (eq : ∀ w<2^33, m' w=m w) (bound : n≤16777216) (h : Good o k msg regs m n) :
    Good o k msg regs' m' n := by
  have mg : MsgGood o k msg regs m' n :=
    msg_congr o k msg regs m m' n (fun w _ hw => eq w hw) bound h.msgs
  refine ⟨⟨mg.messages,mg.key,mg.group,mg.pending,?_,mg.previous⟩,⟨?_,?_,?_⟩⟩
  · intro i hi a
    obtain ⟨p1,p2,p3,p4⟩ := h.msgs.prefetched i hi a
    exact ⟨(er _).trans p1,(er _).trans p2,(er _).trans p3,(er _).trans p4⟩
  · intro i hi ex;apply Eq.trans _ (h.cells.children i hi ex);funext j
    apply eq;have := j.isLt;unfold qLeaf qSource;omega
  · intro g hg;apply Eq.trans _ (h.cells.replies g hg);funext j
    apply eq;have := j.isLt;unfold replyWord qSource;split <;> omega
  · intro g hg j hj;exact (eq _ (by unfold qSource;omega)).trans (h.cells.padding g hg j hj)

theorem fixed_packet_good (o : Oracle) (k : BitVec 192) (msg : Message) (s : MachineState)
    (i : Index) (r : PacketRegs s i.val) (h : Good o k msg s.getReg (memoryView s) i.val) :
    Good o k msg ((plan i.val).foldl (fixedStep o) s).getReg (memoryView ((plan i.val).foldl (fixedStep o) s)) (i.val+1) := by
  let v : View := ⟨s.getReg,memoryView s⟩
  have mat:=matches_ops o s v _ (walk_post _ _ _ (packet_walk s i.val i.isLt r)).1 (matches_initial s)
  exact good_congr o k msg _ _ _ _ _ mat.1 mat.2 (by have := i.isLt;exact Nat.succ_le_of_lt this)
    (good_step o k msg v i h r.msg)

end TwoPermutationPrototype.Grouped
