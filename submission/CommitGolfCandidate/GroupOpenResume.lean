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
  rintro (x|x|x|x|⟨q,hq,m,hm,e⟩) <;> (try unfold rebuiltWord blockWord at e) <;> omega

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
  refine ⟨⟨?_,r.heap,?_,r.salt,r.dest,r.leaves,r.slots,inp,?_,r.base,r.mark,(by rw [r.shift]; simpa using r.heap),r.capLeaves,r.start,
    ?_⟩,?_⟩
  · simpa only [ite_eq_right (Nat.ne_of_lt p0)] using start
  · simpa using r.indices
  · rw [r.endReg]
    unfold indexAt
    congr 1
    have base : indicesBase = 9395245088 := rfl
    omega
  · intro prior present
    have ix := (sortedIndex p prior present).isLt
    have facts := pointer_address_inside (sortedIndex p prior present).val ix
    have order := nonces_end_at_indices
    have records := indices_before_records
    rw [← inp (pointerAddress (sortedIndex p prior present).val) facts.2.1 (by omega) facts.1, pointer_address_word,
      ← pos_present p prior present]
    change memoryView s _=_
    rw [r.pointer prior present, quad_address_node]
    rfl
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

theorem pos_of_mem (p : Positions) (idx : Index) (member : idx∈p) : ∃ j, j<p.card ∧ pos p j=idx := by
  have inList : idx∈p.sort (·≤·) := by simpa using member
  obtain ⟨j,hj,hx⟩:=List.mem_iff_getElem.mp inList
  have size : j<p.card := by simpa using hj
  exact ⟨j,size,(pos_present p j size).trans hx⟩

/-- The level-0 source of an opened position (the commit's node of the sibling quartet) is untouched by the pass. -/
theorem kept_quad (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192) (s : MachineState)
    (r : Ready td p k s p.card) (idx : Index) :
    trapdoorQuad (s:=actual) (virtualTd s) idx=trapdoorQuad (s:=actual) td idx := by
  have ix : idx.val<16777216:=idx.isLt
  set h:=idx.val/4^^^1 with hh
  have hx : h<4194304 := xor_one_lt (idx.val/4) 22 (by omega) (by decide)
  have tb : trapdoorBase=4294971424 := rfl
  have nw : nodeWordOf h=603980292+128*(2*(h/2))+21-4*(h%2) := rfl
  have q := quad_address_node idx.val
  rw [← hh] at q
  have n1 : trapdoorBase≤8*nodeWordOf h := by rw [tb,nw]; omega
  have n2 : 8*nodeWordOf h-trapdoorBase+32≤5100273664 := by rw [tb,nw]; omega
  have v := kept_slice td p k s r (8*nodeWordOf h-trapdoorBase) 4 (by decide) (by rw [tb]; omega) (by omega)
    (fun c hc => by
      rw [show 536871428+(8*nodeWordOf h-trapdoorBase)/8+c=nodeWordOf h+c by rw [tb]; omega]
      exact node_untouched p p.card h c hx hc)
  unfold trapdoorQuad
  rw [q]
  exact v

/-- The block rebuilt for an opened quartet: the inverse of its group reply. -/
theorem placed_block (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (seen : Seen o k td p s p.card) (idx : Index) (member : idx∈p) :
    (virtualTd s).extractLsb' (8*(32*LENGTH+512+1024*(idx.val/4))) 1600=
      o.permutation.symm (groupReply td (idx.val/4)) := by
  obtain ⟨j,hj,who⟩ := pos_of_mem p idx member
  have ix : idx.val<16777216:=idx.isLt
  have b0 := seen.block j hj
  rw [who] at b0
  set q:=idx.val/4 with hq
  have qs : q<4194304 := by omega
  have off : 8*replyWord q=trapdoorBase+groupReplyOffset q := by
    unfold replyWord groupReplyOffset blockWord trapdoorBase LENGTH LOG_LENGTH; split <;> omega
  have win : packBuffer (window (memoryView (actual.initialState .opening (td,p))) (replyWord q))=groupReply td q := by
    rw [←read_permutation_window,off]
    exact input_trapdoor_slice actual actual_layout td p _ 200
      (by change _≤5100273664; unfold groupReplyOffset LENGTH LOG_LENGTH; split <;> omega)
  have v : (virtualTd s).extractLsb' (8*(32*LENGTH+512+1024*q)) 1600=readBuffer s (8*rebuiltWord q) 200 := by
    rw [show 8*rebuiltWord q=trapdoorBase+(32*LENGTH+512+1024*q) by
      unfold rebuiltWord blockWord trapdoorBase LENGTH LOG_LENGTH; omega]
    exact virtual_slice s _ 200 (by change _≤5100273664; unfold LENGTH LOG_LENGTH; omega)
  rw [v]
  apply aligned_buffer_eq _ _ 200 (by decide)
  intro c hc
  rw [b0 c (by omega), win]
  rfl

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
