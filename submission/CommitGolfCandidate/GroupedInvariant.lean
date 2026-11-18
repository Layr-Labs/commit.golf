import CommitGolfCandidate.GroupedContent

/-! Pair-heads leaf-body invariant: what memory holds after `P` pair packets. -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf digestWords)
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate.Permutation.CounterSalt (coord input salts localCoord hpl)
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000

noncomputable def value (o : Oracle) (k : BitVec 192) (m : Message) (i : Index) :=
  pairFullLeafDigests (BiPermutation.equiv Block o.permutation) m (salts o.permutation k) i

/-! ## Salt-source bookkeeping -/

theorem loop_head (n : Nat) (hn : n<16777216) :
    (loopMap n).1=headPair (n/2)-(if ¬pairHead ((n/2)%2048) ∧ copyIndex (n%4096)=9 then 5 else 0) := by
  have e1 : n%4096/2=n/2%2048 := by omega
  have e2 : n/4096=n/2/2048 := by omega
  have e3 : n%4096%2=n%2 := by omega
  unfold loopMap localLoop headPair groupK pairRank copyIndex pairHead
  dsimp only
  rw [e1,e2,e3]
  split_ifs <;> omega

theorem loop_offset (n : Nat) (hn : n<16777216) (nh : ¬pairHead ((n/2)%2048)) :
    (loopMap n).2=(if copyIndex (n%4096)=9 then 144 else 16+16*copyIndex (n%4096)) := by
  have e1 : n%4096/2=n/2%2048 := by omega
  have e3 : n%4096%2=n%2 := by omega
  unfold loopMap localLoop copyIndex pairHead at *
  dsimp only at *
  rw [e1,e3]
  split_ifs <;> omega

theorem salt_head_lt (n : Nat) (hn : n<16777216) (nh : ¬pairHead ((n/2)%2048)) : saltHead n<n/2 := by
  have e := loop_head n hn
  have g : saltHead n=(loopMap n).1 := by rw [loop_map_eq n hn]
  have kpos : groupK (n/2) ≠ 0 := fun z => nh ((pair_head_iff _).mpr z)
  have kle : groupK (n/2) ≤ n/2 := by unfold groupK pairRank; split_ifs <;> omega
  rw [g,e]; unfold headPair; split <;> omega

theorem src_word_eq (n : Nat) (hn : n<16777216) (nh : ¬pairHead ((n/2)%2048)) :
    srcWord n=replyWord (saltHead n)+sliceByte (coord ⟨n,hn⟩).2.val/8 := by
  have e := loop_head n hn
  have f := loop_offset n hn nh
  have g : saltHead n=(loopMap n).1 := by rw [loop_map_eq n hn]
  have g2 : sliceByte (coord ⟨n,hn⟩).2.val=(loopMap n).2 := by rw [loop_map_eq n hn]
  have ci := copy_index_any (n%4096)
  rw [g,g2,e,f]
  unfold srcWord
  by_cases c9 : copyIndex (n%4096)=9
  · simp [c9,nh]
  · simp only [c9,and_false,ite_false,Nat.sub_zero]; omega

/-- The generator input of head pair `P` is the counter-mode input of every leaf whose salt it holds. -/
theorem generated_eq (o : Oracle) (m : Memory) (P : Nat) (limit : P<2^23) (key : BitVec 192)
    (intact : KeyIntact m key) (idx : Index) (src : saltHead idx.val=P) :
    generatedP o m P=groupReply o key idx := by
  unfold generatedP groupReply
  apply congrArg o.permutation
  rw [←reply_pack (input (coord idx).1 key)]
  apply congrArg packBuffer;funext j
  rw [input_word,src]
  have hj := j.isLt
  have far : msgWord (2*P+1)+32 ≤ qSalt 0 := by unfold msgWord qSalt; omega
  have far2 : msgWord (2*P)+64 ≤ qSalt 0 := by unfold msgWord qSalt; omega
  simp only [window,counterState,write_word_at]
  by_cases zero : j.val=0
  · simp [zero]
  · rw [if_neg (by omega),if_neg zero,stateO_at,dif_neg (by omega),dif_neg (by omega)]
    exact intact _ (by omega) hj

theorem slice_word (z : Words 25) (s : Fin 11) (j : Fin 2) :
    Counter.slice z s j=z ⟨sliceByte s.val/8+j.val,by unfold sliceByte; have := s.isLt; have := j.isLt; split <;> omega⟩ := by
  unfold Counter.slice sliceByte; congr 1; apply Fin.ext; simp only; split <;> omega

theorem head_salt_head (P : Nat) (limit : P<2^23) (head : pairHead (P%2048)) (par : Nat) (hp : par<2) :
    saltHead (2*P+par)=P := by
  have e := loop_head (2*P+par) (by omega)
  have g : saltHead (2*P+par)=(loopMap (2*P+par)).1 := by rw [loop_map_eq _ (by omega)]
  rw [show (2*P+par)/2=P by omega] at e
  rw [g,e,if_neg (fun h => h.1 head)]
  unfold headPair; rw [(pair_head_iff P).mp head]; rfl

theorem head_slot_byte (P : Nat) (limit : P<2^23) (head : pairHead (P%2048)) (par : Nat) (hp : par<2) :
    sliceByte (coord ⟨2*P+par,by change 2*P+par<16777216; omega⟩).2.val=184*par := by
  have g := loop_map_eq (2*P+par) (by omega)
  have l : (loopMap (2*P+par)).2=184*par := by
    have e1 : (2*P+par)%4096/2=P%2048 := by omega
    have e3 : (2*P+par)%4096%2=par := by omega
    unfold loopMap localLoop pairHead at *
    dsimp only
    rw [e1,e3]
    split_ifs <;> omega
  rw [g] at l; simpa using l

theorem src_word_low (n : Nat) (hn : n<16777216) (nh : ¬pairHead ((n/2)%2048)) :
    srcWord n+2 ≤ msgWord (2*(n/2))-25 := by
  have ci := copy_index_any (n%4096)
  have kpos : groupK (n/2) ≠ 0 := fun z => nh ((pair_head_iff _).mpr z)
  have kle : groupK (n/2) ≤ n/2 := by unfold groupK pairRank; split_ifs <;> omega
  unfold srcWord replyWord headPair msgWord
  split_ifs <;> omega

theorem stateO_low (o : Oracle) (m : Memory) (P x : Nat) (hx : x<msgWord (2*P)-25) : stateO o m P x=m x := by
  have eO : msgWord (2*P+1)=msgWord (2*P)+32 := by unfold msgWord; omega
  rw [stateO_at,dif_neg (by omega),dif_neg (by omega)]

/-- At a pair 11m+10 the prefetched registers a4..a7 hold the salts it stores (`PrefetchOK` gives this). -/
def RegSalts (rg : Reg → Word) (m : Memory) (P : Nat) : Prop :=
  fromRegs (P%2048) → rg .x14=m (srcWord (2*P)) ∧ rg .x15=m (srcWord (2*P)+1) ∧
    rg .x16=m (srcWord (2*P+1)) ∧ rg .x17=m (srcWord (2*P+1)+1)

theorem copy_state_at (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23) (nh : ¬pairHead (P%2048))
    (pf : RegSalts rg m P) (w : Nat) :
    copyState o rg m P w=
      if w=msgWord (2*P+1)+9 then m (srcWord (2*P+1)+1) else if w=msgWord (2*P+1)+8 then m (srcWord (2*P+1))
      else if w=msgWord (2*P+1)-14 then m (srcWord (2*P)+1) else if w=msgWord (2*P+1)-15 then m (srcWord (2*P))
      else stateO o m P w := by
  have l0 := src_word_low (2*P) (by omega) (by rwa [show 2*P/2=P by omega])
  have l1 := src_word_low (2*P+1) (by omega) (by rwa [show (2*P+1)/2=P by omega])
  rw [show 2*P/2=P by omega] at l0
  rw [show (2*P+1)/2=P by omega] at l1
  have eO : msgWord (2*P+1)=msgWord (2*P)+32 := by unfold msgWord; omega
  have v0 := stateO_low o m P (srcWord (2*P)) (by omega)
  have v1 := stateO_low o m P (srcWord (2*P)+1) (by omega)
  have v2 := stateO_low o m P (srcWord (2*P+1)) (by omega)
  have v3 := stateO_low o m P (srcWord (2*P+1)+1) (by omega)
  unfold copyState; dsimp only
  split
  · rename_i t
    obtain ⟨r0,r1,r2,r3⟩ := pf t
    simp only [write_word_at,r0,r1,r2,r3]
  simp only [write_word_at,v0,v1,v2,v3,
    show srcWord (2*P)+1 ≠ msgWord (2*P+1)-15 by omega,
    show srcWord (2*P+1) ≠ msgWord (2*P+1)-15 by omega,show srcWord (2*P+1) ≠ msgWord (2*P+1)-14 by omega,
    show srcWord (2*P+1)+1 ≠ msgWord (2*P+1)-15 by omega,show srcWord (2*P+1)+1 ≠ msgWord (2*P+1)-14 by omega,
    show srcWord (2*P+1)+1 ≠ msgWord (2*P+1)+8 by omega,ite_false]

/-! ## The invariant -/

/-- Copied salts are ready at their source words once their head pair has run. -/
def SaltsReady (o : Oracle) (k : BitVec 192) (m : Memory) (P : Nat) : Prop :=
  ∀ i : Index, 2*P ≤ i.val → ¬pairHead ((i.val/2)%2048) → saltHead i.val<P →
    (window m (srcWord i.val) : Words 2)=saltWords (salts o.permutation k i)

structure Good (o : Oracle) (k : BitVec 192) (msg : Message) (m : Memory) (P : Nat) : Prop where
  messages : ∀ i : Index, 2*P ≤ i.val → window m (msgWord i.val)=messageWords msg i
  children : ∀ i : Index, i.val<2*P → window m (qLeaf i.val)=digestWords (value o k msg i)
  padding : ∀ g<4194304, ∀ j<9, m (qSource g+j)=0
  key : KeyIntact m k
  ready : SaltsReady o k m P

attribute [local irreducible] packBuffer

/-- The salt words a pair's second calls read are the leaves' counter-mode salts. -/
theorem pair_salts (o : Oracle) (rg : Reg → Word) (k : BitVec 192) (msg : Message) (m : Memory) (P : Nat) (limit : P<2^23)
    (good : Good o k msg m P) (pf : RegSalts rg m P) (par : Nat) (hp : par<2) :
    (fun j : Fin 2 => saltedState o rg m P (msgWord (2*P+par)+(17-9*par)+j.val))=
      saltWords (salts o.permutation k ⟨2*P+par,by change 2*P+par<16777216; omega⟩) := by
  let idx : Index := ⟨2*P+par,by change 2*P+par<16777216; omega⟩
  have eE : msgWord (2*P)=512+64*P := by unfold msgWord; omega
  have eO : msgWord (2*P+1)=544+64*P := by unfold msgWord; omega
  have ePar : msgWord (2*P+par)=512+64*P+32*par := by unfold msgWord; omega
  funext j
  have hj := j.isLt
  unfold saltedState
  split
  · rename_i head
    rw [salt_slice,slice_word]
    have src := head_salt_head P limit head par hp
    have gen := generated_eq o m P limit k good.key idx src
    have byte := head_slot_byte P limit head par hp
    unfold headState
    rw [write_window_at,dif_pos (by omega),← gen]
    unfold replyWords; congr 2
    simp only [idx] at byte ⊢
    rw [byte]; omega
  · rename_i nh
    have nh' : ¬pairHead ((idx.val/2)%2048) := by simpa [idx,show (2*P+par)/2=P by omega] using nh
    have lt := salt_head_lt idx.val idx.isLt nh'
    have rdy := good.ready idx (by simp [idx]) nh' (by simp only [idx] at lt ⊢; omega)
    have w := congrFun rdy j
    simp only [window] at w
    rw [← w,copy_state_at o rg m P limit nh pf]
    rcases (show par=0 ∨ par=1 by omega) with rfl | rfl
    · rcases (show j.val=0 ∨ j.val=1 by omega) with h | h
      · rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]; simp [idx,h]
      · rw [if_neg (by omega),if_neg (by omega),if_pos (by omega)]; simp [idx,h]
    · rcases (show j.val=0 ∨ j.val=1 by omega) with h | h
      · rw [if_neg (by omega),if_pos (by omega)]; simp [idx,h]
      · rw [if_pos (by omega)]; simp [idx,h]

/-! ## Digests -/

theorem even_salts (o : Oracle) (rg : Reg → Word) (k : BitVec 192) (msg : Message) (m : Memory) (P : Nat) (limit : P<2^23)
    (good : Good o k msg m P) (pf : RegSalts rg m P) :
    (fun j : Fin 2 => saltedState o rg m P (msgWord (2*P)+17+j.val))=
      saltWords (salts o.permutation k ⟨2*P,by change 2*P<16777216; omega⟩) := by
  have g := pair_salts o rg k msg m P limit good pf 0 (by decide)
  simpa using g

theorem odd_salts (o : Oracle) (rg : Reg → Word) (k : BitVec 192) (msg : Message) (m : Memory) (P : Nat) (limit : P<2^23)
    (good : Good o k msg m P) (pf : RegSalts rg m P) :
    (fun j : Fin 2 => saltedState o rg m P (msgWord (2*P+1)+8+j.val))=
      saltWords (salts o.permutation k ⟨2*P+1,by change 2*P+1<16777216; omega⟩) := by
  have g := pair_salts o rg k msg m P limit good pf 1 (by decide)
  simpa using g

theorem even_digest (o : Oracle) (rg : Reg → Word) (k : BitVec 192) (msg : Message) (m : Memory) (P : Nat) (limit : P<2^23)
    (good : Good o k msg m P) (pf : RegSalts rg m P) :
    lowDigest (replyWords (digestE o rg m P))=digestWords (value o k msg ⟨2*P,by change 2*P<16777216; omega⟩) := by
  let idx : Index := ⟨2*P,by change 2*P<16777216; omega⟩
  have msgEq := good.messages idx (by simp [idx])
  have win := even_window o rg m P limit (messageWords msg idx) msgEq
  rw [even_salts o rg k msg m P limit good pf] at win
  have first : replyE o m P=(evenFirstRow o.permutation (messageWords msg idx)).2 := by
    unfold replyE evenFirstRow; apply congrArg o.permutation; apply congrArg packBuffer
    funext j; rw [← msgEq]; simp only [window,evenFirstInput,idx]; congr 1; omega
  have reply : digestE o rg m P=(evenSecondRow o.permutation idx (saltWords (salts o.permutation k idx))
      (evenFirstRow o.permutation (messageWords msg idx)).2 (messageWords msg idx)).2 := by
    unfold digestE evenSecondRow; rw [win,first]
  have ev : idx.val%2=0 := by simp [idx]
  change _=digestWords (pairLeafDigest o.permutation idx (saltWords (salts o.permutation k idx)) (messageWords msg idx))
  rw [pair_leaf_even _ _ _ _ ev]
  unfold evenLeafDigest; rw [reply]
  funext j;exact low_digest_word _ j

theorem odd_digest (o : Oracle) (rg : Reg → Word) (k : BitVec 192) (msg : Message) (m : Memory) (P : Nat) (limit : P<2^23)
    (good : Good o k msg m P) (pf : RegSalts rg m P) :
    lowDigest (replyWords (digestO o rg m P))=digestWords (value o k msg ⟨2*P+1,by change 2*P+1<16777216; omega⟩) := by
  let idx : Index := ⟨2*P+1,by change 2*P+1<16777216; omega⟩
  have msgEq := good.messages idx (by simp [idx])
  have win := odd_window o rg m P limit (messageWords msg idx) msgEq
  rw [odd_salts o rg k msg m P limit good pf] at win
  have eE : msgWord (2*P+1)=msgWord (2*P)+32 := by unfold msgWord; omega
  have first : replyO o m P=(pinnedFirstRow o.permutation (messageWords msg idx)).2 := by
    unfold replyO pinnedFirstRow; apply congrArg o.permutation; apply congrArg packBuffer
    funext j; rw [← msgEq]; simp only [window,pinnedFirstInput,idx]
    unfold stateE; rw [write_window_at,dif_neg (by omega)]
  have reply : digestO o rg m P=(pinnedSecondRow o.permutation idx (saltWords (salts o.permutation k idx))
      (pinnedFirstRow o.permutation (messageWords msg idx)).2 (messageWords msg idx)).2 := by
    unfold digestO pinnedSecondRow; rw [win]; try rw [first]
  have od : idx.val%2=1 := by simp only [idx]; omega
  change _=digestWords (pairLeafDigest o.permutation idx (saltWords (salts o.permutation k idx)) (messageWords msg idx))
  rw [pair_leaf_odd _ _ _ _ od]
  unfold pinnedLeafDigest; rw [reply]
  funext j;exact low_digest_word _ j

/-! ## Frames of one pair packet and the invariant step -/

private theorem pair_bounds (P : Nat) (limit : P<2^23) :
    msgWord (2*P+1)=msgWord (2*P)+32 ∧ 25 ≤ msgWord (2*P) ∧ msgWord (2*P+1)+32 ≤ qSource 0 ∧
    qSource 0 ≤ qLeaf (2*P) ∧ qLeaf (2*P+1)=qLeaf (2*P)+4 ∧ qLeaf (2*P+1)+25 ≤ qSalt 0 := by
  refine ⟨by unfold msgWord; omega,by unfold msgWord; omega,by unfold msgWord qSource; omega,
    by unfold qLeaf qSource; omega,by unfold qLeaf; rw [show (2*P+1)/4=2*P/4 by omega]; omega,
    QuartetCommit.qleaf_below_salts (2*P+1) (by omega)⟩

/-- Words below the pair's message window are untouched. -/
theorem pair_mem_low (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23) (w : Nat) (h : w<msgWord (2*P)-25) :
    pairPacketMem o rg m P w=m w := by
  obtain ⟨eO,lo,hq,ql,qn,qs⟩ := pair_bounds P limit
  unfold pairPacketMem taggedO stateE2 taggedE
  rw [write_window_at,dif_neg (by omega),write_word_at,if_neg (by omega),write_window_at,dif_neg (by omega),
    write_word_at,if_neg (by omega),salted_eq_stateO o rg m P w (Or.inl (by omega)) (by omega),stateO_low o m P w h]

/-- Message-region words above the pair's window are untouched. -/
theorem pair_mem_high (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23) (w : Nat)
    (lo : msgWord (2*P+1)+32 ≤ w) (hi : w<qSource 0) : pairPacketMem o rg m P w=m w := by
  obtain ⟨eO,l25,hq,ql,qn,qs⟩ := pair_bounds P limit
  have hk : w ≠ qSalt 0 := by unfold qSource at hi; unfold qSalt; omega
  unfold pairPacketMem taggedO stateE2 taggedE
  rw [write_window_at,dif_neg (by omega),write_word_at,if_neg (by omega),write_window_at,dif_neg (by omega),
    write_word_at,if_neg (by omega),salted_eq_stateO o rg m P w (Or.inr (by omega)) hk,stateO_at,
    dif_neg (by omega),dif_neg (by omega)]

/-- Quartet-region words outside the pair's two digest windows (and not the counter word) are untouched. -/
theorem pair_mem_quartet (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23) (w : Nat)
    (lo : qSource 0 ≤ w) (out : w<qLeaf (2*P) ∨ qLeaf (2*P+1)+25 ≤ w) (hk : w ≠ qSalt 0) :
    pairPacketMem o rg m P w=m w := by
  obtain ⟨eO,l25,hq,ql,qn,qs⟩ := pair_bounds P limit
  unfold pairPacketMem taggedO stateE2 taggedE
  rw [write_window_at,dif_neg (by omega),write_word_at,if_neg (by omega),write_window_at,dif_neg (by omega),
    write_word_at,if_neg (by omega),salted_eq_stateO o rg m P w (Or.inr (by omega)) hk,stateO_at,
    dif_neg (by omega),dif_neg (by omega)]

theorem pair_window_even (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23) :
    (window (pairPacketMem o rg m P) (qLeaf (2*P)) : Words 4)=lowDigest (replyWords (digestE o rg m P)) := by
  obtain ⟨eO,l25,hq,ql,qn,qs⟩ := pair_bounds P limit
  have far : msgWord (2*P+1)+7<qLeaf (2*P) := by omega
  funext j; have hj := j.isLt
  simp only [window,pairPacketMem,taggedO,stateE2]
  rw [write_window_at,dif_neg (by omega),write_word_at,if_neg (by omega),write_window_at,dif_pos (by omega)]
  unfold lowDigest; congr 1; apply Fin.ext; simp

theorem pair_window_odd (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23) :
    (window (pairPacketMem o rg m P) (qLeaf (2*P+1)) : Words 4)=lowDigest (replyWords (digestO o rg m P)) := by
  funext j; have hj := j.isLt
  simp only [window,pairPacketMem]
  rw [write_window_at,dif_pos (by omega)]
  unfold lowDigest; congr 1; apply Fin.ext; simp

theorem salt_head_is_head (n : Nat) (hn : n<16777216) : pairHead ((saltHead n)%2048) := by
  have b := CommitGolfCandidate.Permutation.CounterSalt.local_head_lt (n%4096) (by omega)
  unfold saltHead CommitGolfCandidate.Permutation.CounterSalt.hpl pairHead
  generalize (localCoord (n%4096)).1=l at b ⊢
  have hb : 11*(l/2)+5*(l%2)<2048 := by omega
  rw [show 2048*(n/4096)+(11*(l/2)+5*(l%2))=(11*(l/2)+5*(l%2))+2048*(n/4096) by omega,Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hb]
  rcases Nat.mod_two_eq_zero_or_one l with h|h <;> rw [h] <;> omega

theorem src_word_below (n : Nat) (hn : n<16777216) (nh : ¬pairHead ((n/2)%2048)) :
    srcWord n+2 ≤ msgWord (2*saltHead n+2)-25 ∧ replyWord (saltHead n) ≤ srcWord n ∧
      srcWord n+2 ≤ replyWord (saltHead n)+22 := by
  have sw := src_word_eq n hn nh
  have f := loop_offset n hn nh
  have g2 : sliceByte (coord ⟨n,hn⟩).2.val=(loopMap n).2 := by rw [loop_map_eq n hn]
  have ci := copy_index_any (n%4096)
  have sb : sliceByte (coord ⟨n,hn⟩).2.val ≤ 160 := by rw [g2,f]; split <;> omega
  rw [sw]; unfold replyWord msgWord; refine ⟨by omega,by omega,by omega⟩

theorem pair_mem_reply (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23) (head : pairHead (P%2048)) (w : Nat)
    (lo : replyWord P ≤ w) (hi : w<replyWord P+22) :
    pairPacketMem o rg m P w=replyWords (generatedP o m P) ⟨w-replyWord P,by omega⟩ := by
  obtain ⟨eO,l25,hq,ql,qn,qs⟩ := pair_bounds P limit
  have rw' : replyWord P=msgWord (2*P+1)-15 := rfl
  unfold pairPacketMem taggedO stateE2 taggedE
  rw [write_window_at,dif_neg (by omega),write_word_at,if_neg (by omega),write_window_at,dif_neg (by omega),
    write_word_at,if_neg (by omega)]
  unfold saltedState; rw [if_pos head]; unfold headState; rw [write_window_at,dif_pos (by omega)]
  rfl

private theorem qleaf_before (i P a : Nat) (h : i<2*P) (ha : a<4) : qLeaf i+a<qLeaf (2*P) := by
  have := QuartetCommit.qleaf_before i (2*P) h; omega

theorem good_step (o : Oracle) (rg : Reg → Word) (k : BitVec 192) (msg : Message) (m : Memory) (P : Nat) (limit : P<2^23)
    (good : Good o k msg m P) (pf : RegSalts rg m P) : Good o k msg (pairPacketMem o rg m P) (P+1) := by
  obtain ⟨eO,l25,hq,ql,qn,qs⟩ := pair_bounds P limit
  constructor
  · intro i hi
    rw [← good.messages i (by omega)]; funext a
    have ha := a.isLt; have ix : i.val<16777216 := i.isLt
    simp only [window]
    apply pair_mem_high o rg m P limit
    · have : msgWord (2*P+2) ≤ msgWord i.val := by unfold msgWord; omega
      have : msgWord (2*P+2)=msgWord (2*P+1)+32 := by unfold msgWord; omega
      omega
    · unfold msgWord qSource; omega
  · rintro ⟨n,hn⟩ hi
    dsimp only at hi
    by_cases e : n=2*P
    · subst e
      show (window (pairPacketMem o rg m P) (qLeaf (2*P)) : Words 4)=_
      rw [pair_window_even o rg m P limit,even_digest o rg k msg m P limit good pf]
    · by_cases e1 : n=2*P+1
      · subst e1
        show (window (pairPacketMem o rg m P) (qLeaf (2*P+1)) : Words 4)=_
        rw [pair_window_odd o rg m P limit,odd_digest o rg k msg m P limit good pf]
      · rw [← good.children ⟨n,hn⟩ (by show n<2*P; omega)]; funext a
        have ha := a.isLt
        simp only [window]
        have b := qleaf_before n P a.val (by omega) ha
        apply pair_mem_quartet o rg m P limit _ _ (Or.inl b)
        · have : qLeaf (2*P)<qSalt 0 := by omega
          omega
        · have : qSource 0 ≤ qLeaf n := by unfold qLeaf qSource; omega
          omega
  · intro g hg j hj
    rw [← good.padding g hg j hj]
    apply pair_mem_quartet o rg m P limit _ (by unfold qSource; omega) _ (by unfold qSource qSalt; omega)
    have o0 := QuartetCommit.qpad_outside g j (2*P) hj
    have o1 := QuartetCommit.qpad_outside g j (2*P+1) hj
    omega
  · intro j lo up
    rw [← good.key j lo up]
    exact pair_mem_quartet o rg m P limit _ (by unfold qSource qSalt; omega) (Or.inr (by omega)) (by omega)
  · rintro ⟨n,hn⟩ hi nh lt
    dsimp only at hi nh lt
    have sb := src_word_below n hn nh
    by_cases old : saltHead n<P
    · rw [← good.ready ⟨n,hn⟩ (by show 2*P ≤ n; omega) nh old]; funext a
      have ha := a.isLt
      simp only [window]
      apply pair_mem_low o rg m P limit
      have mono : msgWord (2*saltHead n+2) ≤ msgWord (2*P) := by unfold msgWord; omega
      omega
    · have eq : saltHead n=P := by omega
      have head := salt_head_is_head n hn
      have sw := src_word_eq n hn nh
      rw [eq] at head sb sw
      rw [salt_slice]; funext a
      have ha := a.isLt
      rw [slice_word]
      simp only [window]
      rw [pair_mem_reply o rg m P limit head _ (by omega) (by omega),generated_eq o m P limit k good.key ⟨n,hn⟩ eq]
      congr 2; omega

theorem good_congr (o : Oracle) (k : BitVec 192) (msg : Message) (m m' : Memory) (P : Nat)
    (eq : ∀ w<2^33, m' w=m w) (_bound : P≤2^23) (h : Good o k msg m P) : Good o k msg m' P := by
  constructor
  · intro i hi;apply Eq.trans _ (h.messages i hi);funext j
    apply eq;have := j.isLt;have ix : i.val<16777216:=i.isLt;unfold msgWord;omega
  · intro i hi;apply Eq.trans _ (h.children i hi);funext j
    apply eq;have := j.isLt;have ix : i.val<16777216:=i.isLt;unfold qLeaf qSource;omega
  · intro g hg j hj;exact (eq _ (by unfold qSource;omega)).trans (h.padding g hg j hj)
  · intro j hj hi;exact (eq _ (by unfold qSalt;omega)).trans (h.key j hj hi)
  · intro i hi nh lt;apply Eq.trans _ (h.ready i hi nh lt);funext j
    have ix : i.val<16777216:=i.isLt
    have sb := src_word_below i.val ix nh
    have : saltHead i.val<2^23 := by omega
    apply eq;have := j.isLt;unfold msgWord at sb;omega

/-! ## The prefetch registers -/

/-- Between head 11m (m ≤ 185) and pair 11m+10, a6,a7 hold table salt 8 of head 11m's reply; between head 11m+5 and
pair 11m+10, a4,a5 hold table salt 8 of head 11m+5's reply. -/
def PrefetchOK (rg : Reg → Word) (m : Memory) (P : Nat) : Prop :=
  (1 ≤ P%2048%11 ∧ P%2048<2046 →
    rg .x16=m (replyWord (P-P%2048%11)+18) ∧ rg .x17=m (replyWord (P-P%2048%11)+19)) ∧
  (6 ≤ P%2048%11 →
    rg .x14=m (replyWord (P-P%2048%11+5)+18) ∧ rg .x15=m (replyWord (P-P%2048%11+5)+19))

theorem reg_salts_of (rg : Reg → Word) (m : Memory) (P : Nat) (h : PrefetchOK rg m P) : RegSalts rg m P := by
  intro t
  unfold fromRegs at t
  obtain ⟨a6,a7⟩ := h.1 ⟨by omega,by omega⟩
  obtain ⟨a4,a5⟩ := h.2 (by omega)
  have hk : groupK P=5 := by unfold groupK pairRank; rw [t]; rfl
  have l1 : P%2048 ≤ P := Nat.mod_le _ _
  have l2 : P%2048%11 ≤ P%2048 := Nat.mod_le _ _
  have l3 : P%2048<2048 := Nat.mod_lt _ (by decide)
  have p10 : 10 ≤ P := by omega
  have m2 : (2*P)%4096=2*(P%2048) := Nat.mul_mod_mul_left 2 P 2048
  have m3 : (2*P+1)%4096=2*(P%2048)+1 := by
    rw [Nat.add_mod,m2,show 1%4096=1 by decide]; exact Nat.mod_eq_of_lt (by omega)
  have s0 : srcWord (2*P)=replyWord (P-P%2048%11+5)+18 := by
    have c8 : copyIndex ((2*P)%4096)=8 := by
      unfold copyIndex; dsimp only
      rw [m2,show 2*(P%2048)/2%11=P%2048%11 by omega,show 2*(P%2048)%2=0 by omega,t]; rfl
    unfold srcWord; rw [c8,if_neg (by decide),show 2*P/2=P by omega]
    unfold headPair; rw [hk,t,show P-10+5=P-5 by omega]
  have s1 : srcWord (2*P+1)=replyWord (P-P%2048%11)+18 := by
    have c9 : copyIndex ((2*P+1)%4096)=9 := by
      unfold copyIndex; dsimp only
      rw [m3,show (2*(P%2048)+1)/2%11=P%2048%11 by omega,show (2*(P%2048)+1)%2=1 by omega,t]; rfl
    unfold srcWord; rw [c9,if_pos rfl,show (2*P+1)/2=P by omega]
    unfold headPair; rw [hk,t,show P-5-5=P-10 by omega]
  rw [s0,s1]
  exact ⟨a4,a5,a6,a7⟩

theorem prefetch_initial (rg : Reg → Word) (m : Memory) : PrefetchOK rg m 0 :=
  ⟨fun h => absurd h.1 (by decide),fun h => absurd h (by decide)⟩

theorem prefetch_congr (rg rg' : Reg → Word) (m m' : Memory) (P : Nat) (bound : P ≤ 2^23)
    (er : ∀ r, rg' r=rg r) (em : ∀ w<2^33, m' w=m w) (h : PrefetchOK rg m P) : PrefetchOK rg' m' P := by
  have b (h : Nat) (hh : h ≤ P) (j : Nat) (hj : j<20) : replyWord h+j<2^33 := by unfold replyWord msgWord; omega
  refine ⟨fun c => ?_,fun c => ?_⟩
  · obtain ⟨x,y⟩ := h.1 c
    rw [er,er,em _ (b (P-P%2048%11) (by omega) 18 (by omega)),em _ (b (P-P%2048%11) (by omega) 19 (by omega))]
    exact ⟨x,y⟩
  · obtain ⟨x,y⟩ := h.2 c
    have : P-P%2048%11+5 ≤ P := by omega
    rw [er,er,em _ (b (P-P%2048%11+5) this 18 (by omega)),em _ (b (P-P%2048%11+5) this 19 (by omega))]
    exact ⟨x,y⟩

private theorem reply_low (P h j : Nat) (hh : h<P) (hj : j<20) : replyWord h+j<msgWord (2*P)-25 := by
  unfold replyWord msgWord; omega

private theorem head_reply_word (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23)
    (head : pairHead (P%2048)) (j : Nat) (lo : 18 ≤ j) (hj : j<20) :
    pairPacketMem o rg m P (replyWord P+j)=headState o m P (msgWord (2*P+1)+(j-15)) := by
  have big : 15 ≤ msgWord (2*P+1) := by unfold msgWord; omega
  have rw' : replyWord P=msgWord (2*P+1)-15 := rfl
  rw [pair_mem_reply o rg m P limit head _ (by omega) (by omega)]
  unfold headState
  rw [write_window_at,dif_pos (by omega)]
  congr 1; apply Fin.ext; (try simp only [Fin.val_mk]); omega

theorem prefetch_step (o : Oracle) (rg rg' : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23)
    (h : PrefetchOK rg m P)
    (r14 : rg' .x14=if P%2048%11=5 then headState o m P (msgWord (2*P+1)+3) else rg .x14)
    (r15 : rg' .x15=if P%2048%11=5 then headState o m P (msgWord (2*P+1)+4) else rg .x15)
    (r16 : rg' .x16=if prefetchA (P%2048) then headState o m P (msgWord (2*P+1)+3) else rg .x16)
    (r17 : rg' .x17=if prefetchA (P%2048) then headState o m P (msgWord (2*P+1)+4) else rg .x17) :
    PrefetchOK rg' (pairPacketMem o rg m P) (P+1) := by
  have l1 : P%2048 ≤ P := Nat.mod_le _ _
  have l2 : P%2048%11 ≤ P%2048 := Nat.mod_le _ _
  have l3 : P%2048<2048 := Nat.mod_lt _ (by decide)
  by_cases edge : P%2048=2047
  · have e : (P+1)%2048=0 := by omega
    refine ⟨fun c => ?_,fun c => ?_⟩ <;> rw [e] at c <;> simp at c
  have e : (P+1)%2048=P%2048+1 := by omega
  refine ⟨fun c => ?_,fun c => ?_⟩
  · rw [e] at c ⊢
    by_cases z : P%2048%11=0
    · have a : prefetchA (P%2048) := by unfold prefetchA; exact ⟨z,by omega⟩
      have head : pairHead (P%2048) := Or.inl z
      have hb : P+1-(P%2048+1)%11=P := by omega
      rw [hb,r16,r17,if_pos a,if_pos a,head_reply_word o rg m P limit head 18 (by omega) (by omega),
        head_reply_word o rg m P limit head 19 (by omega) (by omega)]
      exact ⟨rfl,rfl⟩
    · have na : ¬prefetchA (P%2048) := by unfold prefetchA; exact fun a => z a.1
      have r1 : 1 ≤ P%2048%11 := by omega
      have r9 : P%2048%11 ≤ 9 := by omega
      have hb : P+1-(P%2048+1)%11=P-P%2048%11 := by omega
      obtain ⟨x,y⟩ := h.1 ⟨r1,by omega⟩
      rw [hb,r16,r17,if_neg na,if_neg na,
        pair_mem_low o rg m P limit _ (reply_low P (P-P%2048%11) 18 (by omega) (by omega)),
        pair_mem_low o rg m P limit _ (reply_low P (P-P%2048%11) 19 (by omega) (by omega))]
      exact ⟨x,y⟩
  · rw [e] at c ⊢
    by_cases f : P%2048%11=5
    · have head : pairHead (P%2048) := Or.inr f
      have hb : P+1-(P%2048+1)%11+5=P := by omega
      rw [hb,r14,r15,if_pos f,if_pos f,head_reply_word o rg m P limit head 18 (by omega) (by omega),
        head_reply_word o rg m P limit head 19 (by omega) (by omega)]
      exact ⟨rfl,rfl⟩
    · have r6 : 6 ≤ P%2048%11 := by omega
      have hb : P+1-(P%2048+1)%11+5=P-P%2048%11+5 := by omega
      obtain ⟨x,y⟩ := h.2 r6
      rw [hb,r14,r15,if_neg f,if_neg f,
        pair_mem_low o rg m P limit _ (reply_low P (P-P%2048%11+5) 18 (by omega) (by omega)),
        pair_mem_low o rg m P limit _ (reply_low P (P-P%2048%11+5) 19 (by omega) (by omega))]
      exact ⟨x,y⟩

theorem fixed_pair_good (o : Oracle) (k : BitVec 192) (msg : Message) (s : MachineState) (P : Nat) (limit : P<2^23)
    (r : PairRegs s P) (h : Good o k msg (memoryView s) P) (pf : PrefetchOK s.getReg (memoryView s) P) :
    Good o k msg (memoryView ((pairPlan P).foldl (fixedStep o) s)) (P+1) ∧
      PrefetchOK ((pairPlan P).foldl (fixedStep o) s).getReg (memoryView ((pairPlan P).foldl (fixedStep o) s)) (P+1) := by
  let v : View := ⟨s.getReg,memoryView s⟩
  have mat := matches_ops o s v _ (walk_post _ _ _ (pair_walk s P limit r)).1 (matches_initial s)
  have eq := pair_plan_meaning o v P
  have regs := pair_plan_regs o v P
  have mm := mat.2; rw [eq] at mm
  refine ⟨good_congr o k msg _ _ _ mm (by omega) (good_step o s.getReg k msg _ P limit h (reg_salts_of _ _ _ pf)),?_⟩
  exact prefetch_congr _ _ _ _ _ (by omega) mat.1 mm
    (prefetch_step o s.getReg _ (memoryView s) P limit pf regs.1 regs.2.1 regs.2.2.1 regs.2.2.2)

end TwoPermutationPrototype.Grouped
