import CommitGolfCandidate.GroupedStores
import CommitGolfCandidate.GroupedTailEval
import CommitGolfCandidate.GroupedPhysicalBase
import CommitGolfCandidate.GroupedQMeaning
import CommitGolfCandidate.QuartetPhysical
import CommitGolfCandidate.MaterializedManifest

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf qUpper digestWords pairLeaf pairHeap upper_sequence_semantics upper_groups_semantics UpperContent PaddedLeaves pair_heap_parent pair_heap_leaf packed_sequence_keeps_output wide_parent_full_register)
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer checkEvaluation qGroups qUnits scan fixedScan packedParentsTrace packedParentGroups rootPrefix pairHeap pairLeaf readyState
attribute [local irreducible] savedKey
theorem serialize (parents : MachineState) (heap raw : Nat → BitVec 256) (key : Key)
    (res : Execution) (state : res.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (outReg : parents.getReg .x8=4294971392) (stores : FinalStores parents heap raw key) :
    let output := actual.readCommit res
    output.1=heap 1 ∧
      (∀ n, 0<n → n<8388608 → Opening.trapdoorHeap (s:=actual) output.2 n=heap n) ∧
      (∀ i : Index, QuartetRV.trapdoorLeaf (s:=actual) output.2 i.val=raw i.val) ∧
      (∀ j : Fin 3, savedKey output.2 j=key.extractLsb' (64*j.val) 64) := by
  have out : actual.layout.commitment=4294971392:=rfl
  have td : actual.layout.trapdoor=4294971424:=rfl
  have size : actual.sizes.trapdoor=2952790016:=rfl
  simp only [Opening.trapdoorHeap,QuartetRV.trapdoorLeaf,QuartetRV.trapdoorSalt,Submission.readCommit,state,out,td]
  refine ⟨(root_copy_output parents heapReg outReg).trans (stores.nodes 1 (by decide) (by decide)),?_,?_,?_⟩
  · intro n pos small
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 actual.sizes.trapdoor (32*n) 32 (by rw [size];omega)
    rw [show 8*(32*n)=256*n by omega,show 4294971424+32*n=8*treeWord n by unfold treeWord;omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold treeWord;omega) (by unfold treeWord;omega) (by decide)]
    exact stores.nodes n pos small
  · intro i;have hi : i.val<16777216 := i.isLt
    let off := 32*LENGTH+512*(i.val/4)+72+32*(i.val%4)
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 actual.sizes.trapdoor off 32
      (by rw [size];dsimp [off,LENGTH,LOG_LENGTH];omega)
    rw [show 4294971424+off=8*qLeaf i.val by dsimp [off,qLeaf,qSource,LENGTH,LOG_LENGTH];omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold qLeaf qSource;omega) (by unfold qLeaf qSource;omega) (by decide)]
    exact stores.children i
  · intro j
    unfold savedKey
    have hj:=j.isLt
    let off:=2684354568+8*j.val
    have slice:=read_buffer_slice (rootPrefix parents 10) 4294971424 actual.sizes.trapdoor off 8
      (by rw [size];dsimp [off];omega)
    rw [show 4294971424+off=8*(qSalt 0+1+j.val) by dsimp [qSalt,off];omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 8 (by unfold qSalt;omega) (by unfold qSalt;omega) (by decide),read_word]
    exact stores.keyWords j


end TwoPermutationPrototype.Grouped
