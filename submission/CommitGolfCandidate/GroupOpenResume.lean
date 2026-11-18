import CommitGolfCandidate.GroupOpenFixed
import CommitGolfCandidate.GroupOpenProofBytes

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks machineMarks sortedIndex)
open TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 20000
set_option maxHeartbeats 1400000

theorem boundary_at_end (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (p0 : 0<p.card) (r : Ready td p k s p.card) :
    RecordBoundary actual (virtualTd s) p (s.setPC 0x103c) 0 ∧ RecordMarks p s 0 := by
  have inp := virtual_input td p s (by
    intro a lo hi alg
    let w:=a/8
    have ea : a=8*w := by dsimp [w];omega
    have wlo : 905970180≤w := by dsimp [trapdoorBase,trapdoorBytes,LENGTH,LOG_LENGTH] at lo;omega
    have wlim : w<2^33 := by
      have lim : proofBase<2^36:=by decide
      omega
    have h:=r.frame w wlim (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr wlo)
    rw [ea];exact h)
  have start : (s.setPC 0x103c).pc=0x103c := rfl
  refine ⟨⟨?_,r.heap,?_,r.salt,r.dest,r.leaves,r.slots,inp,?_,r.base,r.mark,r.cap,r.capLeaves,r.start,r.mult⟩,?_⟩
  · simpa only [ite_eq_right (Nat.ne_of_lt p0)] using start
  · simpa using r.indices
  · simpa using r.count
  · intro node hn
    have stable := r.frame (512+node) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
    have z := initial_mark_word actual actual_layout image_actual td p node hn
    have addr : BitVec.ofNat 64 (Opening.markBase+8*node)=wordAddress (512+node) := by
      unfold Opening.markBase wordAddress;congr 1 <;> omega
    have zz : memoryView (actual.initialState .opening (td,p)) (512+node)=0 := by simpa only [addr,memoryView] using z
    simpa [Opening.groupsBefore,machineMarks,addr,memoryView] using stable.trans zz

theorem kept_slice (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192) (s : MachineState)
    (r : Ready td p k s p.card) (off cells : Nat) (size : cells≤8) (a : off%8=0)
    (endAt : off+8*cells≤2684354560) :
    (virtualTd s).extractLsb' (8*off) (8*(8*cells))=td.extractLsb' (8*off) (8*(8*cells)) := by
  have room : off+8*cells≤trapdoorBytes := by change _≤2952790016;omega
  rw [virtual_slice s off _ (by rwa [actual_layout.trapdoorSize]),←input_trapdoor_slice actual actual_layout td p off _ room]
  apply Opening.copied_buffer _ _ _ _ _ (by unfold trapdoorBase LENGTH LOG_LENGTH;omega)
    (by unfold trapdoorBase LENGTH LOG_LENGTH;omega) size
  intro i hi
  let w:=(trapdoorBase+off+8*i)/8
  have ea : trapdoorBase+off+8*i=8*w := by dsimp [w,trapdoorBase,LENGTH,LOG_LENGTH];omega
  have lower : 217≤w := by dsimp [w,trapdoorBase,LENGTH,LOG_LENGTH];omega
  have upper : w<872415748 := by dsimp [w,trapdoorBase,LENGTH,LOG_LENGTH];omega
  exact ea ▸ r.frame w (by omega) (Or.inr (by omega)) (Or.inr lower) (Or.inl upper)

theorem kept_tree (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192) (s : MachineState)
    (r : Ready td p k s p.card) :
    (∀ n, n<8388608 → Opening.trapdoorHeap (s:=actual) (virtualTd s) n=Opening.trapdoorHeap (s:=actual) td n) ∧
    (∀ i : Index, trapdoorLeaf (s:=actual) (virtualTd s) i.val=trapdoorLeaf (s:=actual) td i.val) := by
  constructor
  · intro n hi
    have v:=kept_slice td p k s r (32*n) 4 (by decide) (by omega) (by omega)
    simpa only [Opening.trapdoorHeap,←Nat.mul_assoc] using v
  · intro i;have hi : i.val<16777216:=i.isLt
    unfold trapdoorLeaf
    exact kept_slice td p k s r _ 4 (by decide) (by dsimp [LENGTH,LOG_LENGTH];omega) (by dsimp [LENGTH,LOG_LENGTH];omega)

theorem selected_salt (o : Oracle) (k : BitVec 192) (p : Positions) (s : MachineState)
    (seen : Seen o k p s p.card) (idx : Index) (member : idx∈p) :
    trapdoorSalt (s:=actual) (virtualTd s) idx=salts o.permutation k idx := by
  have iBound : idx.val<16777216:=idx.isLt
  have inList : idx∈p.sort (·≤·) := by simpa using member
  obtain ⟨j,hj,hx⟩:=List.mem_iff_getElem.mp inList
  have size : j<p.card := by simpa using hj
  have who : pos p j=idx := (pos_present p j size).trans hx
  unfold trapdoorSalt
  rw [virtual_slice s _ 16 (by change 160*16777216+16*idx.val+16≤2952790016;omega)]
  rw [show trapdoorBase+(160*LENGTH+16*idx.val)=8*(872415748+2*idx.val) by unfold trapdoorBase LENGTH LOG_LENGTH;omega]
  apply aligned_buffer_eq _ _ 16 (by decide)
  intro b hb
  have h:=seen j size (⟨b,hb⟩ : Fin 2)
  dsimp only at h;rw [who] at h
  have addr : destAt idx+BitVec.ofNat 64 (8*b)=wordAddress (872415748+2*idx.val+b) := by
    unfold destAt wordAddress;rw [←BitVec.ofNat_add];congr 1 <;> omega
  rw [addr] at h;exact h

end TwoPermutationPrototype.GroupedOpening
