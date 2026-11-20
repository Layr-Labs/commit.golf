import CommitGolfCandidate.GroupedQMeaning
import CommitGolfCandidate.GroupedPhysicalBase
import CommitGolfCandidate.QuartetWordBridge
import CommitGolfCandidate.QuartetRVModel
import CommitGolfCandidate.TwoPermutationRootBytes
import CommitGolfCandidate.TwoPermutationBindingLeaf

/-!
# Reading the final trapdoor

`unit_pairs`: from the body's hand-over (`TailReady`), every unit's words `[s_u, s_u+64)` hold the two
heap leaves `2^22 + 2U` (low: the node of group `2U+1`, odd reply bytes `168..200`) and `2^22 + 2U + 1` (high: the
node of group `2U`, even reply bytes `0..32`). `k3_serialize`: after the tail and the root copy, the commitment is
heap node 1 and the trapdoor holds the heap nodes below `2^22`, every group reply and the key words.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCommit (physicalHeap physical_heap_leaf)
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer rootPrefix physicalHeap

private theorem low_of_pair (a b : BitVec 256) (k : Nat) (hk : k<4) :
    (a ++ b).extractLsb' (64*k) 64=b.extractLsb' (64*k) 64 := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  rw [BitVec.getLsbD_append,if_pos (by omega)]

private theorem high_of_pair (a b : BitVec 256) (k : Nat) (lo : 4≤k) (hk : k<8) :
    (a ++ b).extractLsb' (64*k) 64=a.extractLsb' (64*(k-4)) 64 := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  rw [BitVec.getLsbD_append,if_neg (by omega)]
  congr 1;omega

private theorem slice_of_slice {w : Nat} (x : BitVec w) (a k : Nat) (hk : k<4) :
    (x.extractLsb' a 256).extractLsb' (64*k) 64=x.extractLsb' (a+64*k) 64 := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,show 64*k+i<256 by omega]
  congr 1;omega

private theorem reply_pack (v : BitVec 1600) : packBuffer (replyWords v)=v := by
  apply BitVec.eq_of_getLsbD_eq;intro k hk
  let j : Fin 25 := ⟨k/64,by omega⟩
  have h:=congrArg (fun w : BitVec 64 => w.getLsbD (k%64)) (packed_word (replyWords v) j)
  have b : k%64<64 := by omega
  unfold replyWords at h
  dsimp only [j] at h
  change ((packBuffer _).extractLsb' (64*(k/64)) 64).getLsbD (k%64) =
    (v.extractLsb' (64*(k/64)) 64).getLsbD (k%64) at h
  unfold replyWords
  simpa only [BitVec.getLsbD_extractLsb',b,decide_true,Bool.true_and,Nat.div_add_mod] using h

/-- The level-21 inputs in place: unit `u`'s words hold `node_odd ‖ node_even` (heap leaves `2^22+2U`, `2^22+2U+1`). -/
theorem unit_pairs (o : Oracle) (msg : Message) (r : CompleteSaltTape) (key : BitVec 192) (m : Memory)
    (ready : TailReady o (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) msg r) key m) :
    UnitPairs m (physicalHeap o msg r) := by
  intro U hU k hk
  have x0 : (2*U)^^^1=2*U+1 := by rw [Quartet.xor_one_cases];split <;> omega
  have x1 : (2*U+1)^^^1=2*U := by rw [Quartet.xor_one_cases];split <;> omega
  rw [physical_heap_leaf o msg r (2*U+1) (by omega),physical_heap_leaf o msg r (2*U) (by omega),x0,x1]
  generalize pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) msg r = d at ready ⊢
  have w0 : groupReplyWord (2*U)=unitBase U+4 := by
    unfold groupReplyWord;rw [if_pos (by omega),show 2*U/2=U by omega]
  have w1 : groupReplyWord (2*U+1)=unitBase U-21 := by
    unfold groupReplyWord;rw [if_neg (by omega),show (2*U+1)/2=U by omega]
  rw [quartet_node_even (show (2*U)%2=0 by omega),quartet_node_odd (show (2*U+1)%2=1 by omega)]
  by_cases low : k<4
  · rw [low_of_pair _ _ k low,slice_of_slice _ _ k low]
    have word : m (unitBase U+k)=(o.permutation (quartetEncode (Quartet.quartetPayload d (2*U+1)))).extractLsb'
        (64*(21+k)) 64 := by
      have h := congrFun (ready.replies (2*U+1) (by omega)) ⟨21+k,by omega⟩
      have addr : unitBase U+k=groupReplyWord (2*U+1)+(21+k) := by
        rw [w1];unfold unitBase unitFirst cellFirst;omega
      rw [addr];exact h
    rw [word];congr 1;omega
  · rw [high_of_pair _ _ k (by omega) hk]
    unfold outputDigest
    rw [slice_of_slice _ _ (k-4) (by omega)]
    have word : m (unitBase U+k)=(o.permutation (quartetEncode (Quartet.quartetPayload d (2*U)))).extractLsb'
        (64*(k-4)) 64 := by
      have h := congrFun (ready.replies (2*U) (by omega)) ⟨k-4,by omega⟩
      have addr : unitBase U+k=groupReplyWord (2*U)+(k-4) := by rw [w0];omega
      rw [addr];exact h
    rw [word];congr 1;omega

/-- Reading the final trapdoor. -/
theorem k3_serialize (parents : MachineState) (heap : Nat → BitVec 256) (before : Memory)
    (o : Oracle) (d : DigestTape) (key : BitVec 192)
    (res : Execution) (state : res.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (outReg : parents.getReg .x8=4294971392) (content : TailContent parents heap before 0)
    (ready : TailReady o d key before) :
    let output := actual.readCommit res
    output.1=heap 1 ∧
      (∀ n, 0<n → n<4194304 → Opening.trapdoorHeap (s:=actual) output.2 n=heap n) ∧
      (∀ g, g<4194304 → trapdoorGroupReply output.2 g=o.permutation (quartetEncode (Quartet.quartetPayload d g))) ∧
      (∀ j : Fin 3, savedKey output.2 j=key.extractLsb' (64*j.val) 64) := by
  have out : actual.layout.commitment=4294971392:=rfl
  have td : actual.layout.trapdoor=4294971424:=rfl
  have size : actual.sizes.trapdoor=5100273664:=rfl
  simp only [Opening.trapdoorHeap,trapdoorGroupReply,Submission.readCommit,state,out,td]
  refine ⟨(root_copy_output parents heapReg outReg).trans (content.nodes 1 (by decide) (by decide)),?_,?_,?_⟩
  · intro n pos small
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 actual.sizes.trapdoor (32*n) 32 (by rw [size];omega)
    rw [show 8*(32*n)=256*n by omega,show 4294971424+32*n=8*treeWord n by unfold treeWord;omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold treeWord;omega) (by unfold treeWord;omega) (by decide)]
    exact content.nodes n pos small
  · intro g hg
    have bound : 8*groupReplyWord g-4294971424+200 ≤ actual.sizes.trapdoor := by
      rw [size];unfold groupReplyWord unitBase unitFirst cellFirst unitStride;split <;> omega
    have above : 4294971424 ≤ 8*groupReplyWord g := by
      unfold groupReplyWord unitBase unitFirst cellFirst unitStride;split <;> omega
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 actual.sizes.trapdoor (groupReplyOffset g) 200 bound
    rw [show 4294971424+groupReplyOffset g=8*groupReplyWord g by unfold groupReplyOffset trapdoorBase;omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 200 above
      (by unfold groupReplyWord unitBase unitFirst cellFirst unitStride;split <;> omega) (by decide),
      read_permutation_window]
    have same : (window (memoryView parents) (groupReplyWord g) : Words 25)=window before (groupReplyWord g) := by
      funext k
      exact content.high _ (by unfold groupReplyWord unitBase unitFirst unitFloor cellFirst unitStride;split <;> omega)
        (by have := k.isLt;unfold groupReplyWord unitBase unitFirst cellFirst unitStride;split <;> omega)
    rw [same,ready.replies g hg]
    exact reply_pack _
  · intro j
    unfold savedKey
    have hj:=j.isLt
    let off:=4831838216+8*j.val
    have slice:=read_buffer_slice (rootPrefix parents 10) 4294971424 actual.sizes.trapdoor off 8
      (by rw [size];dsimp [off];omega)
    rw [show 4294971424+off=8*(keyWord+j.val) by dsimp [off,keyWord];omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 8 (by unfold keyWord;omega) (by unfold keyWord;omega) (by decide),
      read_word]
    exact (content.high _ (by unfold keyWord unitFloor cellFirst;omega) (by unfold keyWord;omega)).trans (ready.key j)

end TwoPermutationPrototype.Grouped
