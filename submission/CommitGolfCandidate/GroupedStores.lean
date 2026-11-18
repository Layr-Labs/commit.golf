import CommitGolfCandidate.GroupedPhysicalBase
import CommitGolfCandidate.GroupedQMeaning
import CommitGolfCandidate.QuartetPhysicalInputs
import CommitGolfCandidate.QuartetRVModel
import CommitGolfCandidate.TwoPermutationRootBytes
import CommitGolfCandidate.MaterializedManifest

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf qUpper digestWords originalLeaf physicalHeap upper_sequence_semantics upper_groups_semantics UpperContent PaddedLeaves physical_heap_parent physical_heap_leaf packed_sequence_keeps_output wide_parent_full_register)
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer checkEvaluation qGroups qUnits scan fixedScan packedParentsTrace packedParentGroups rootPrefix physicalHeap originalLeaf readyState
structure FinalStores (s : MachineState) (heap raw : Nat → BitVec 256) (key : Key) : Prop where
  nodes : ∀ n, 0<n → n<8388608 → nodeDigest s n=heap n
  children : ∀ i : Index, readBuffer s (8*qLeaf i.val) 32=raw i.val
  keyWords : ∀ j : Fin 3, memoryView s (qSalt 0+1+j.val)=key.extractLsb' (64*j.val) 64

theorem finish_stores (s leafState : MachineState) (heap raw : Nat → BitVec 256) (key : Key)
    (p : UpperContent s heap (memoryView leafState) 0) (l : PaddedLeaves (memoryView leafState) (fun i => digestWords (raw i)))
    (saved : KeyIntact (memoryView leafState) key) : FinalStores s heap raw key := by
  refine ⟨p.nodes,?_,?_⟩
  · intro i;apply aligned_buffer_eq _ _ _ (by decide);intro k hk
    have hi : i.val<16777216:=i.isLt
    exact (p.high _ (by unfold qLeaf qSource;omega) (by unfold qLeaf qSource;omega)).trans
      (congrFun (l.2 i.val hi) (⟨k,hk⟩ : Fin 4))
  · intro j;have hj:=j.isLt
    have hi:=saved (1+j.val) (by omega) (by omega)
    rw [←Nat.add_assoc] at hi
    exact (p.high _ (by unfold qSalt qSource;omega) (by unfold qSalt;omega)).trans (by simpa [keyBlock] using hi)


end TwoPermutationPrototype.Grouped
