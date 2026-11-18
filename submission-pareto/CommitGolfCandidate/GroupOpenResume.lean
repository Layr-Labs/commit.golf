import CommitGolfCandidate.GroupOpenFixed
import CommitGolfCandidate.GroupOpenHeaderSpec
import CommitGolfCandidate.GroupOpenProofBytes
import CommitGolfCandidate.TwoPermutationHeapInvariant

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks machineMarks sortedIndex)
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 20000
set_option maxHeartbeats 1400000

theorem untouched_low (p : Positions) (j w : Nat)
    (h : w<128 ∨ (153≤w ∧ w<192) ∨ (217≤w ∧ w<553648644) ∨ (570425860≤w ∧ w<603980292) ∨ 1174405636≤w) :
    ¬Touched p j w := by
  have := top_le p j
  rintro (x|x|x|x|⟨q,hq,_,m,hm,e⟩) <;> (try unfold replyEWord blockWord at e) <;> omega

theorem untouched_block (p : Positions) (j q c : Nat) (hq : q<4194304) (hc : c<128) (nd3 : ¬(q%2=0 ∧ 21≤c ∧ c<25)) :
    ¬Touched p j (blockWord q+c) := by
  have := top_le p j
  rintro (x|x|x|x|⟨q',hq',e',m,hm,e⟩) <;> unfold blockWord at * <;> (try unfold replyEWord blockWord at e) <;> omega

theorem boundary_at_end (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (p0 : 0<p.card) (r : Ready td p k s p.card) :
    RecordBoundary actual (virtualTd s) p s 0 ∧ RecordMarks p s 0 := by
  have inp := virtual_input td p s (by
    intro a lo hi alg
    let w:=a/8
    have ea : a=8*w := by dsimp [w];omega
    have wlo : 1174405636≤w := by dsimp [trapdoorBase,trapdoorBytes,LENGTH,LOG_LENGTH] at lo;omega
    have wlim : w<2^33 := by
      have lim : proofBase<2^36:=by decide
      omega
    have h:=r.frame w wlim (untouched_low p p.card w (Or.inr (Or.inr (Or.inr (Or.inr wlo)))))
    rw [ea];exact h)
  have start : s.pc=0x103c := by simpa [passPC,address] using r.pc
  refine ⟨⟨?_,r.heap,?_,r.salt,r.dest,r.leaves,r.slots,inp,?_,r.base,r.mark,r.cap,r.capLeaves,r.start⟩,?_⟩
  · simpa only [ite_eq_right (Nat.ne_of_lt p0)] using start
  · simpa using r.indices
  · simpa using r.count
  · intro node hn
    have stable := r.frame (512+node) (by omega) (untouched_low p p.card _ (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))
    have z := initial_mark_word actual actual_layout image_actual td p node hn
    have addr : BitVec.ofNat 64 (Opening.markBase+8*node)=wordAddress (512+node) := by
      unfold Opening.markBase wordAddress;congr 1 <;> omega
    have zz : memoryView (actual.initialState .opening (td,p)) (512+node)=0 := by simpa only [addr,memoryView] using z
    simpa [Opening.groupsBefore,machineMarks,addr,memoryView] using stable.trans zz

/-- A trapdoor slice of `cells` words whose words the pass never touched reads the same in the virtual trapdoor. -/
theorem kept_slice (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192) (s : MachineState)
    (r : Ready td p k s p.card) (off cells : Nat) (size : cells≤8) (a : off%8=0) (room : off+8*cells≤5100273664)
    (fresh : ∀ c<cells, ¬Touched p p.card (536871428+off/8+c)) :
    (virtualTd s).extractLsb' (8*off) (8*(8*cells))=td.extractLsb' (8*off) (8*(8*cells)) := by
  have room' : off+8*cells≤trapdoorBytes := by change _≤5100273664;omega
  rw [virtual_slice s off _ (by rwa [actual_layout.trapdoorSize]),←input_trapdoor_slice actual actual_layout td p off _ room']
  apply Opening.copied_buffer _ _ _ _ _ (by unfold trapdoorBase LENGTH LOG_LENGTH;omega)
    (by unfold trapdoorBase LENGTH LOG_LENGTH;omega) size
  intro i hi
  have ea : trapdoorBase+off+8*i=8*(536871428+off/8+i) := by unfold trapdoorBase LENGTH LOG_LENGTH;omega
  rw [ea]
  exact r.frame _ (by omega) (fresh i hi)

theorem kept_heap (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192) (s : MachineState)
    (r : Ready td p k s p.card) (n : Nat) (hn : n<4194304) :
    Opening.trapdoorHeap (s:=actual) (virtualTd s) n=Opening.trapdoorHeap (s:=actual) td n := by
  have v:=kept_slice td p k s r (32*n) 4 (by decide) (by omega) (by omega)
    (fun c hc => untouched_low p p.card _ (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))
  simpa only [Opening.trapdoorHeap,←Nat.mul_assoc] using v

theorem kept_leaf (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192) (s : MachineState)
    (r : Ready td p k s p.card) (i : Index) (keep : ¬(i.val/4%2=0 ∧ i.val%4=3)) :
    trapdoorLeaf (s:=actual) (virtualTd s) i.val=trapdoorLeaf (s:=actual) td i.val := by
  have hi : i.val<16777216:=i.isLt
  unfold trapdoorLeaf
  exact kept_slice td p k s r _ 4 (by decide) (by dsimp [LENGTH,LOG_LENGTH];omega) (by dsimp [LENGTH,LOG_LENGTH];omega)
    (fun c hc => by
      have e : 536871428+(32*LENGTH+1024*(i.val/4)+72+32*(i.val%4))/8+c=blockWord (i.val/4)+(9+4*(i.val%4)+c) := by
        unfold blockWord LENGTH LOG_LENGTH; omega
      rw [e]; exact untouched_block p p.card _ _ (by omega) (by omega) (by omega))

theorem pos_of_mem (p : Positions) (idx : Index) (member : idx∈p) : ∃ j, j<p.card ∧ pos p j=idx := by
  have inList : idx∈p.sort (·≤·) := by simpa using member
  obtain ⟨j,hj,hx⟩:=List.mem_iff_getElem.mp inList
  have size : j<p.card := by simpa using hj
  exact ⟨j,size,(pos_present p j size).trans hx⟩

/-- The level-22 sibling of an opened quartet, copied from the commit's group node. -/
theorem placed_sibling (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (seen : Seen o k td p s p.card) (idx : Index) (member : idx∈p) :
    Opening.trapdoorHeap (s:=actual) (virtualTd s) (4194304+(idx.val/4^^^1))=
      td.extractLsb' (8*(8*nodeWordOf (idx.val/4^^^1)-trapdoorBase)) 256 := by
  obtain ⟨j,hj,who⟩ := pos_of_mem p idx member
  have ix : idx.val<16777216:=idx.isLt
  have sib0 := seen.sibling j hj
  rw [who] at sib0
  set h:=idx.val/4^^^1 with hh
  have hx : h<4194304 := xor_one_lt (idx.val/4) 22 (by omega) (by decide)
  have tb : trapdoorBase=4294971424 := rfl
  have nw : nodeWordOf h=603980292+128*(2*(h/2))+42+4*(h%2) := rfl
  have n1 : trapdoorBase≤8*nodeWordOf h := by rw [tb,nw]; omega
  have n2 : 8*nodeWordOf h-trapdoorBase+32≤5100273664 := by rw [tb,nw]; omega
  have n3 : (8*nodeWordOf h)%8=0 := by omega
  unfold Opening.trapdoorHeap
  rw [show 256*(4194304+h)=8*(32*(4194304+h)) by omega,
    show BitVec.extractLsb' (8*(32*(4194304+h))) 256 (virtualTd s)=BitVec.extractLsb' (8*(32*(4194304+h))) (8*32) (virtualTd s) from rfl,
    show BitVec.extractLsb' (8*(8*nodeWordOf h-trapdoorBase)) 256 td=BitVec.extractLsb' (8*(8*nodeWordOf h-trapdoorBase)) (8*32) td from rfl,
    virtual_slice s _ 32 (by change _≤5100273664;omega),
    ←input_trapdoor_slice actual actual_layout td p _ 32 (by change _≤5100273664;omega),
    show trapdoorBase+(8*nodeWordOf h-trapdoorBase)=8*nodeWordOf h by omega]
  apply Opening.copied_buffer _ _ (8*nodeWordOf h) _ 4 n3 (by rw [tb]; omega) (by decide)
  intro c hc
  have sib := sib0 c hc
  have e1 : trapdoorBase+32*(4194304+h)+8*c=8*(heapWord (4194304+h)+c) := by rw [tb]; unfold heapWord; omega
  have e2 : 8*nodeWordOf h+8*c=8*(nodeWordOf h+c) := by omega
  rw [e1,e2]; exact sib

/-- The d3 of an opened even quartet: bits 1344..1600 of the inverse of its group reply. -/
theorem placed_d3 (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (seen : Seen o k td p s p.card) (idx : Index) (member : idx∈p) (even : idx.val/4%2=0) :
    trapdoorLeaf (s:=actual) (virtualTd s) (4*(idx.val/4)+3)=
      (o.permutation.symm (td.extractLsb' (8*(32*LENGTH+1024*(idx.val/4)+168)) 1600)).extractLsb' 1344 256 := by
  obtain ⟨j,hj,who⟩ := pos_of_mem p idx member
  have ix : idx.val<16777216:=idx.isLt
  have d0 := seen.d3 j hj (by rw [who]; exact even)
  rw [who] at d0
  set q:=idx.val/4 with hq
  have win : packBuffer (window (memoryView (actual.initialState .opening (td,p))) (replyEWord q))=
      td.extractLsb' (8*(32*LENGTH+1024*q+168)) 1600 := by
    rw [←read_permutation_window,show 8*replyEWord q=trapdoorBase+(32*LENGTH+1024*q+168) by
      unfold replyEWord blockWord trapdoorBase LENGTH LOG_LENGTH; omega]
    exact input_trapdoor_slice actual actual_layout td p _ 200 (by change _≤5100273664;unfold LENGTH LOG_LENGTH;omega)
  unfold trapdoorLeaf
  rw [show 32*LENGTH+1024*((4*q+3)/4)+72+32*((4*q+3)%4)=32*LENGTH+1024*q+168 by unfold LENGTH LOG_LENGTH; omega]
  rw [show (256:Nat)=8*32 from rfl,virtual_slice s _ 32 (by change _≤5100273664;unfold LENGTH LOG_LENGTH;omega),
    show trapdoorBase+(32*LENGTH+1024*q+168)=8*replyEWord q by unfold replyEWord blockWord trapdoorBase LENGTH LOG_LENGTH;omega]
  apply aligned_buffer_eq _ _ 32 (by decide)
  intro c hc
  have d := d0 c (by omega)
  rw [win] at d
  rw [d, nested_slice _ (by omega : 64*c+64≤256)]
  unfold replyWords; congr 1; simp only [Fin.val_mk]; omega

theorem selected_salt (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) (seen : Seen o k td p s p.card) (idx : Index) (member : idx∈p) :
    trapdoorSalt (s:=actual) (virtualTd s) idx=linkedSalts o k idx := by
  obtain ⟨j,size,who⟩ := pos_of_mem p idx member
  have iBound : idx.val<16777216:=idx.isLt
  unfold trapdoorSalt
  rw [virtual_slice s _ 16 (by change 288*16777216+16*idx.val+16≤5100273664;omega)]
  rw [show trapdoorBase+(288*LENGTH+16*idx.val)=8*(1140851204+2*idx.val) by unfold trapdoorBase LENGTH LOG_LENGTH;omega]
  apply aligned_buffer_eq _ _ 16 (by decide)
  intro b hb
  have h:=seen.salt j size (⟨b,hb⟩ : Fin 2)
  rw [who,salt_word_view] at h
  exact h

end TwoPermutationPrototype.GroupedOpening
