import CommitGolfCandidate.GroupedContent

/-!
# Frames and second-call windows of the K3-lite slots (K1 leaves; c2-level, before the group tail)
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate.Permutation.CounterSalt (coord firstLeaf input parts salts)
set_option maxRecDepth 18000
set_option maxHeartbeats 600000
set_option exponentiation.threshold 2048

theorem ahead_true (i : Index) (h : rank i.val=0) : isAHead i=true := by
  unfold isAHead;unfold rank at h;simp [h]

theorem ahead_false (i : Index) (h : rank i.val≠0) : isAHead i=false := by
  unfold isAHead;unfold rank at h;simp [h]

theorem tag_head (i : Index) (h : rank i.val=0) : pinnedPositionTag i=wordAddress (msgWord i.val-7) := by
  unfold pinnedPositionTag;rw [ahead_true i h];unfold wordAddress msgWord;simp only [if_true];congr 1;omega

theorem tag_follower (i : Index) (h : rank i.val≠0) : pinnedPositionTag i=wordAddress (msgWord i.val+7) := by
  unfold pinnedPositionTag;rw [ahead_false i h];unfold wordAddress msgWord
  simp only [Bool.false_eq_true,if_false];congr 1;omega

private theorem far_key (i : Nat) (hi : i<16777216) : msgWord i+64<qSalt 0 := by
  unfold msgWord qSalt;omega

private theorem far_heap (i j : Nat) (hi : i<16777216) : msgWord i+64<qLeaf j := by
  unfold msgWord qLeaf qSource;omega

theorem window_outside {n : Nat} (m : Memory) (a : Nat) (ws : Words n) (w : Nat)
    (h : w<a ∨ a+n≤w) : writeWindow m a ws w=m w := by unfold writeWindow;apply dif_neg;omega

/-- Away from the key block's counter word, the seeded memory is the memory after the two first calls. -/
theorem seeded_at (o : Oracle) (m : Memory) (i a : Nat) (ha : a≠qSalt 0) : seededMem o m i a=aMem2 o m i a := by
  unfold seededMem;split
  · simp only [writeWord,ha,ite_false]
  · rfl

/-- Every write of slot `i` lies in `[w-25, w+53)`, the counter word or the slot's heap cell. -/
theorem packet_frame (o : Oracle) (regs : Reg → Word) (m : Memory) (i a : Nat) (hi : i<16777216)
    (counter : a≠qSalt 0) (near : a<msgWord i-25 ∨ msgWord i+53≤a) (dst : a<qLeaf i ∨ qLeaf i+25≤a) :
    c2Mem o regs m i a=m a := by
  have sm : 512≤msgWord i := by unfold msgWord;omega
  rw [c2Mem,window_outside _ _ _ _ dst]
  have n1 : ¬(msgWord i-25≤a ∧ a<msgWord i-25+25) := by omega
  have n2 : ¬(msgWord i+28≤a ∧ a<msgWord i+28+25) := by omega
  have n3 : ¬(msgWord i+16≤a ∧ a<msgWord i+16+25) := by omega
  have n4 : ¬(msgWord i-4≤a ∧ a<msgWord i-4+25) := by omega
  have e5 : a≠msgWord i-5 := by omega
  have e7 : a≠msgWord i+7 := by omega
  have e8 : a≠msgWord i+8 := by omega
  have e9 : a≠msgWord i+9 := by omega
  unfold preSecond
  split
  · simp only [headMem,writeWord,writeWindow,n3,e5,ite_false,dite_false]
    rw [seeded_at o m i a counter]
    simp only [aMem2,aMem1,writeWindow,n1,n2,dite_false]
  split
  · simp only [cMem,writeWord,e9,ite_false]
  · unfold followerMem
    split
    · simp only [fMem1,writeWord,writeWindow,n4,e7,e8,e9,ite_false,dite_false]
    split
    · simp only [fMem1,writeWord,writeWindow,n4,e7,e8,e9,ite_false,dite_false]
    · simp only [fMem1,writeWord,writeWindow,n4,e7,e8,e9,ite_false,dite_false]

/-- A C leaf or a follower writes only `[w-4, w+21)` (and its heap cell). -/
theorem follower_frame (o : Oracle) (regs : Reg → Word) (m : Memory) (i a : Nat) (hi : i<16777216)
    (notHead : rank i≠0) (near : a<msgWord i-4 ∨ msgWord i+21≤a) (dst : a<qLeaf i ∨ qLeaf i+25≤a) :
    c2Mem o regs m i a=m a := by
  have sm : 512≤msgWord i := by unfold msgWord;omega
  rw [c2Mem,window_outside _ _ _ _ dst]
  have n4 : ¬(msgWord i-4≤a ∧ a<msgWord i-4+25) := by omega
  have e7 : a≠msgWord i+7 := by omega
  have e8 : a≠msgWord i+8 := by omega
  have e9 : a≠msgWord i+9 := by omega
  unfold preSecond
  rw [if_neg notHead]
  split
  · simp only [cMem,writeWord,e9,ite_false]
  · unfold followerMem
    split
    · simp only [fMem1,writeWord,writeWindow,n4,e7,e8,e9,ite_false,dite_false]
    split
    · simp only [fMem1,writeWord,writeWindow,n4,e7,e8,e9,ite_false,dite_false]
    · simp only [fMem1,writeWord,writeWindow,n4,e7,e8,e9,ite_false,dite_false]

/-- A C leaf writes only its tag `w+9` (and its heap cell). -/
theorem c_frame (o : Oracle) (regs : Reg → Word) (m : Memory) (i a : Nat) (h1 : rank i=1)
    (ne : a≠msgWord i+9) (dst : a<qLeaf i ∨ qLeaf i+25≤a) : c2Mem o regs m i a=m a := by
  rw [c2Mem,window_outside _ _ _ _ dst]
  unfold preSecond
  rw [if_neg (show ¬rank i=0 by omega),if_pos h1]
  simp only [cMem,writeWord,ne,ite_false]

/-- Outside the heap cell, the memory after a slot is the memory before its second call. -/
theorem pre_packet (o : Oracle) (regs : Reg → Word) (m : Memory) (i a : Nat) (dst : a<qLeaf i ∨ qLeaf i+25≤a) :
    preSecond o regs m i a=c2Mem o regs m i a := by
  rw [c2Mem,window_outside _ _ _ _ dst]

theorem new_digest (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) : window (c2Mem o regs m i) (qLeaf i) =
    lowDigest (replyWords (digestReply o regs m i)) := by
  funext k
  have h : qLeaf i≤qLeaf i+k.val ∧ qLeaf i+k.val<qLeaf i+25 := by have := k.isLt;omega
  simp [window,c2Mem,writeWindow,h,lowDigest]

/-- The window `[w+7, w+32)` of a C leaf: salt and reply tail already in place, tag at `w+9`. -/
theorem c_second_window (regs : Reg → Word) (m : Memory) (i : Index) (h : rank i.val≠0)
    (x10 : regs .x10=wordAddress (msgWord i.val+7)) (nonce : Words 2) (first : Words 25)
    (msgw : Words 32) (salt : window m (msgWord i.val+7)=nonce)
    (reply : ∀ j : Fin 11, m (msgWord i.val+10+j.val)=first ⟨14+j.val,by omega⟩)
    (tail : ∀ j : Fin 11, m (msgWord i.val+21+j.val)=msgw ⟨21+j.val,by omega⟩) :
    window (cMem regs m i.val) (msgWord i.val+7)=pinnedSecondInput i nonce first msgw := by
  funext j
  have hj := j.isLt
  simp only [window,cMem,writeWord,pinnedSecondInput,ahead_false i h,Bool.false_eq_true,if_false,tag_follower i h,x10]
  by_cases j2 : j.val=2
  · simp [j2]
  · rw [if_neg (by omega),if_neg j2]
    by_cases jl : j.val<2
    · rw [dif_pos jl,←salt];rfl
    · rw [dif_neg jl]
      by_cases jm : j.val<14
      · rw [dif_pos jm]
        have r := reply ⟨j.val-3,by omega⟩
        simp only [Fin.val_mk] at r
        rw [show msgWord i.val+7+j.val=msgWord i.val+10+(j.val-3) by omega,r]
        congr 1;apply Fin.ext;simp only [Fin.val_mk];omega
      · rw [dif_neg jm]
        have r := tail ⟨j.val-14,by omega⟩
        simp only [Fin.val_mk] at r
        rw [show msgWord i.val+7+j.val=msgWord i.val+21+(j.val-14) by omega,r]
        congr 1;apply Fin.ext;simp only [Fin.val_mk];omega

/-- The salt a follower stores into `w+7, w+8`. -/
def followerSalt (regs : Reg → Word) (m : Memory) (i : Nat) : Words 2 := fun d =>
  if rank i≤8 then m (sourceWord i+d.val)
  else if rank i=9 then (if d.val=0 then regs .x14 else regs .x15)
  else (if d.val=0 then regs .x16 else regs .x17)

theorem source_below (i : Nat) (h0 : rank i≠0) (h1 : rank i≠1) : sourceWord i+2≤msgWord i-4 := by
  have g := genWord_rank i (rank i) rfl
  have : rank i<11 := rank_lt i
  have sm : 512≤msgWord i := by unfold msgWord;omega
  unfold sourceWord;omega


theorem ww_in {n : Nat} (m : Memory) (a : Nat) (ws : Words n) (w : Nat) (h1 : a ≤ w) (h2 : w<a+n) :
    writeWindow m a ws w=ws ⟨w-a,by omega⟩ := by unfold writeWindow;rw [dif_pos ⟨h1,h2⟩]

theorem wd_at (m : Memory) (a : Nat) (v : Word) : writeWord m a v a=v := by unfold writeWord;rw [if_pos rfl]

theorem wd_out (m : Memory) (a : Nat) (v : Word) (w : Nat) (h : w≠a) : writeWord m a v w=m w := by
  unfold writeWord;rw [if_neg h]

/-- Pointwise reads of the memory before the A leaf's second call. -/
theorem head_read_low (o : Oracle) (m : Memory) (i a : Nat) (hi : i<16777216) (lo : msgWord i-25≤a)
    (up : a<msgWord i) (h5 : a≠msgWord i-5) :
    headMem o m i a=replyWords (callReply o m (msgWord i+7)) ⟨a-(msgWord i-25),by omega⟩ := by
  have sm : 512≤msgWord i := by unfold msgWord;omega
  have fk := far_key i hi
  unfold headMem
  rw [wd_out _ _ _ a h5,window_outside (n:=25) _ (msgWord i+16) _ a (Or.inl (by omega)),seeded_at o m i a (by omega),aMem2,window_outside (n:=25) _ (msgWord i+28) _ a (Or.inl (by omega)),aMem1,
    ww_in (n:=25) _ (msgWord i-25) _ a lo (by omega)]

theorem head_read_msg (o : Oracle) (m : Memory) (i a : Nat) (hi : i<16777216) (lo : msgWord i≤a)
    (up : a<msgWord i+16) : headMem o m i a=m a := by
  have sm : 512≤msgWord i := by unfold msgWord;omega
  have fk := far_key i hi
  unfold headMem
  rw [wd_out _ _ _ a (show a≠msgWord i-5 by omega),window_outside (n:=25) _ (msgWord i+16) _ a (Or.inl up),seeded_at o m i a (by omega),aMem2,window_outside (n:=25) _ (msgWord i+28) _ a (Or.inl (by omega)),aMem1,
    window_outside (n:=25) _ (msgWord i-25) _ a (Or.inr (by omega))]

theorem head_read_gen (o : Oracle) (m : Memory) (i a : Nat) (hi : i<16777216) (lo : msgWord i+16≤a)
    (up : a<msgWord i+41) : headMem o m i a=replyWords (generated o m i) ⟨a-(msgWord i+16),by omega⟩ := by
  have sm : 512≤msgWord i := by unfold msgWord;omega
  unfold headMem
  rw [wd_out _ _ _ a (show a≠msgWord i-5 by omega),ww_in (n:=25) _ (msgWord i+16) _ a lo (by omega)]

theorem head_read_c (o : Oracle) (m : Memory) (i a : Nat) (hi : i<16777216) (lo : msgWord i+41≤a)
    (up : a<msgWord i+53) : headMem o m i a=replyWords (cFirst o m i) ⟨a-(msgWord i+28),by omega⟩ := by
  have sm : 512≤msgWord i := by unfold msgWord;omega
  have fk := far_key i hi
  unfold headMem
  rw [wd_out _ _ _ a (show a≠msgWord i-5 by omega),window_outside (n:=25) _ (msgWord i+16) _ a (Or.inr (by omega)),seeded_at o m i a (by omega),aMem2,ww_in (n:=25) _ (msgWord i+28) _ a (by omega) up]

/-- The A leaf's second-call window `[w-7, w+18)`. -/
theorem head_second_window (o : Oracle) (m : Memory) (i : Index) (h : rank i.val=0) :
    window (headMem o m i.val) (msgWord i.val-7) =
      pinnedSecondInput i (Counter.slice (replyWords (generated o m i.val)) 0)
        (replyWords (callReply o m (msgWord i.val+7))) (window m (msgWord i.val)) := by
  have hi : i.val<16777216 := i.isLt
  have sm : 512≤msgWord i.val := by unfold msgWord;omega
  funext j
  have hj := j.isLt
  show headMem o m i.val (msgWord i.val-7+j.val)=_
  simp only [pinnedSecondInput,ahead_true i h,↓reduceIte,if_true]
  by_cases j2 : j.val=2
  · rw [if_pos j2,tag_head i h,show msgWord i.val-7+j.val=msgWord i.val-5 by omega]
    unfold headMem;rw [wd_at]
  rw [if_neg j2]
  by_cases jl : j.val<7
  · rw [dif_pos jl,head_read_low o m i.val (msgWord i.val-7+j.val) hi (by omega) (by omega) (by omega)]
    congr 1;apply Fin.ext;simp only [Fin.val_mk];omega
  rw [dif_neg jl]
  by_cases jm : j.val<23
  · rw [dif_pos jm,head_read_msg o m i.val (msgWord i.val-7+j.val) hi (by omega) (by omega)]
    show m _=m _;congr 1;simp only [Fin.val_mk];omega
  · rw [dif_neg jm,head_read_gen o m i.val (msgWord i.val-7+j.val) hi (by omega) (by omega)]
    simp only [Counter.slice,Counter.sliceStart,Fin.val_zero,↓reduceIte,Nat.zero_add]
    congr 1;apply Fin.ext;simp only [Fin.val_mk];omega

theorem follower_mem_other (o : Oracle) (regs : Reg → Word) (m : Memory) (i a : Nat) (h7 : a≠msgWord i+7)
    (h8 : a≠msgWord i+8) : followerMem o regs m i a=fMem1 o m i a := by
  unfold followerMem
  split
  · rw [wd_out _ _ _ a h8,wd_out _ _ _ a h7]
  split
  · rw [wd_out _ _ _ a h8,wd_out _ _ _ a h7]
  · rw [wd_out _ _ _ a h8,wd_out _ _ _ a h7]

theorem fmem_reply (o : Oracle) (m : Memory) (i a : Nat) (lo : msgWord i-4≤a) (hi : a<msgWord i+21)
    (h9 : a≠msgWord i+9) : fMem1 o m i a=replyWords (callReply o m (msgWord i)) ⟨a-(msgWord i-4),by omega⟩ := by
  unfold fMem1;rw [wd_out _ _ _ a h9,ww_in (n:=25) _ (msgWord i-4) _ a lo (by omega)]

theorem fmem_out (o : Oracle) (m : Memory) (i a : Nat) (out : a<msgWord i-4 ∨ msgWord i+21≤a)
    (h9 : a≠msgWord i+9) : fMem1 o m i a=m a := by
  have sm : 512≤msgWord i := by unfold msgWord;omega
  unfold fMem1;rw [wd_out _ _ _ a h9,window_outside (n:=25) _ (msgWord i-4) _ a (by omega)]

theorem follower_mem_salt (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) (h0 : rank i≠0) (h1 : rank i≠1)
    (d : Fin 2) : followerMem o regs m i (msgWord i+7+d.val)=followerSalt regs m i d := by
  have sb := source_below i h0 h1
  have sm : 512≤msgWord i := by unfold msgWord;omega
  have hd := d.isLt
  have src (e : Nat) (he : e<2) : fMem1 o m i (sourceWord i+e)=m (sourceWord i+e) :=
    fmem_out o m i _ (Or.inl (by omega)) (by omega)
  unfold followerMem followerSalt
  by_cases d0 : d.val=0
  · rw [d0,Nat.add_zero]
    have e78 : msgWord i+7≠msgWord i+8 := by omega
    split
    · rw [wd_out _ _ _ _ e78,wd_at,←Nat.add_zero (sourceWord i),src 0 (by decide)]
    split
    · rw [wd_out _ _ _ _ e78,wd_at,if_pos rfl]
    · rw [wd_out _ _ _ _ e78,wd_at,if_pos rfl]
  · have d1 : d.val=1 := by omega
    rw [d1,show msgWord i+7+1=msgWord i+8 by omega]
    split
    · rw [wd_at,wd_out _ _ _ _ (show sourceWord i+1≠msgWord i+7 by omega),src 1 (by decide)]
    split
    · rw [wd_at,if_neg (show ¬(1=0) by decide)]
    · rw [wd_at,if_neg (show ¬(1=0) by decide)]

/-- A follower's window `[w+7, w+32)`. -/
theorem follower_second_window (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Index)
    (h0 : rank i.val≠0) (h1 : rank i.val≠1) :
    window (followerMem o regs m i.val) (msgWord i.val+7) =
      pinnedSecondInput i (followerSalt regs m i.val) (replyWords (callReply o m (msgWord i.val)))
        (window m (msgWord i.val)) := by
  have sm : 512≤msgWord i.val := by unfold msgWord;omega
  funext j
  have hj := j.isLt
  show followerMem o regs m i.val (msgWord i.val+7+j.val)=_
  simp only [pinnedSecondInput,ahead_false i h0,Bool.false_eq_true,↓reduceIte,if_false]
  by_cases j2 : j.val=2
  · rw [if_pos j2,tag_follower i h0,
      follower_mem_other o regs m i.val (msgWord i.val+7+j.val) (by omega) (by omega),
      show msgWord i.val+7+j.val=msgWord i.val+9 by omega]
    unfold fMem1;rw [wd_at]
  rw [if_neg j2]
  by_cases jl : j.val<2
  · rw [dif_pos jl]
    exact follower_mem_salt o regs m i.val h0 h1 ⟨j.val,jl⟩
  rw [dif_neg jl,follower_mem_other o regs m i.val (msgWord i.val+7+j.val) (by omega) (by omega)]
  by_cases jm : j.val<14
  · rw [dif_pos jm,fmem_reply o m i.val (msgWord i.val+7+j.val) (by omega) (by omega) (by omega)]
    congr 1;apply Fin.ext;simp only [Fin.val_mk];omega
  · rw [dif_neg jm,fmem_out o m i.val (msgWord i.val+7+j.val) (Or.inr (by omega)) (by omega)]
    show m _=m _;congr 1;simp only [Fin.val_mk];omega

/-- After an A slot: the generator reply at `[w+16, w+41)`. -/
theorem head_generator (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) (hi : i<16777216) (h : rank i=0) :
    window (c2Mem o regs m i) (msgWord i+16)=replyWords (generated o m i) := by
  have fh := far_heap i i hi
  funext j
  have hj := j.isLt
  show c2Mem o regs m i (msgWord i+16+j.val)=_
  rw [←pre_packet o regs m i (msgWord i+16+j.val) (Or.inl (by omega))]
  unfold preSecond;rw [if_pos h,head_read_gen o m i (msgWord i+16+j.val) hi (by omega) (by omega)]
  congr 1;apply Fin.ext;simp only [Fin.val_mk];omega

/-- After an A slot: the tail of the C leaf's first reply at `[w+42, w+53)`. -/
theorem head_c_reply (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) (hi : i<16777216) (h : rank i=0)
    (j : Fin 11) : c2Mem o regs m i (msgWord i+42+j.val)=replyWords (cFirst o m i) ⟨14+j.val,by omega⟩ := by
  have fh := far_heap i i hi
  have hj := j.isLt
  rw [←pre_packet o regs m i (msgWord i+42+j.val) (Or.inl (by omega))]
  unfold preSecond;rw [if_pos h,head_read_c o m i (msgWord i+42+j.val) hi (by omega) (by omega)]
  congr 1;apply Fin.ext;simp only [Fin.val_mk];omega

/-- After an A slot: the C leaf's own words from `w+53` on are untouched. -/
theorem head_c_tail (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) (hi : i<16777216) (h : rank i=0)
    (a : Nat) (lo : msgWord i+53≤a) (up : a<msgWord i+64) : c2Mem o regs m i a=m a := by
  have fh := far_heap i i hi
  have fk := far_key i hi
  exact packet_frame o regs m i a hi (by omega) (Or.inr lo) (Or.inl (by omega))

/-- The C leaf's first reply reads its message (the A first call does not touch it). -/
theorem c_first_eq (o : Oracle) (m : Memory) (i : Nat) :
    cFirst o m i=o.permutation (packBuffer (window m (msgWord i+32))) := by
  have sm : 512≤msgWord i := by unfold msgWord;omega
  have e : (window (aMem1 o m i) (msgWord i+32) : Words 25)=window m (msgWord i+32) := by
    funext j
    show aMem1 o m i (msgWord i+32+j.val)=m (msgWord i+32+j.val)
    unfold aMem1
    exact window_outside (n:=25) _ _ _ _ (Or.inr (by omega))
  unfold cFirst callReply;rw [e]

end TwoPermutationPrototype.Grouped
