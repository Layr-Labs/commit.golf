import CommitGolfCandidate.GroupedCommit
import CommitGolfCandidate.GroupedSeededLeaves
import CommitGolfCandidate.GroupedPhysicalBase
import CommitGolfCandidate.K3CUSerial
import CommitGolfCandidate.QuartetRVModel
import CommitGolfCandidate.TwoPermutationRootBytes
import CommitGolfCandidate.TwoPermutationBindingLeaf

/-!
# What the commit outputs

`physical_results`: the commitment is the root of `physicalHeap`; the trapdoor holds every heap node below
`2^22`, every leaf digest except `d3` of an even quartet (it lies under that quartet's group reply), every
quartet group reply, and the key. `counted_commit`: the commit draws the key and makes 43,470,847 public calls.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCommit (originalLeaf physicalHeap physical_heap_parent physical_heap_level21
  physical_heap_240 physical_heap_238 physical_heap_leaf)
open TwoPermutationPrototype.GroupedUpper (l21StartPrefix heapStartPrefix)
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer checkEvaluation scan fixedScan l21Groups packedParentGroups rootPrefix
  physicalHeap readyState seededLeaves packedOutput tailBody

theorem physical_results (oracle : Oracle) (msg : Message) (key : Key) :
    let leaves:=seededLeaves oracle msg key
    let r:=chainSalts oracle key
    let d:=pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) msg r
    let output:=actual.readCommit (packedOutput oracle leaves)
    let heap:=physicalHeap oracle msg r
    output.1=heap 1 ∧ (∀ n, 0<n → n<4194304 → Opening.trapdoorHeap (s:=actual) output.2 n=heap n) ∧
      (∀ i : Index, ¬ overwritten i.val → QuartetRV.trapdoorLeaf (s:=actual) output.2 i.val=originalLeaf oracle msg r i.val) ∧
      (∀ g, g<4194304 → trapdoorGroupReply output.2 g=oracle.permutation (quartetEncode (Quartet.quartetPayload d g))) ∧
      (∀ j : Fin 3, savedKey output.2 j=key.extractLsb' (64*j.val) 64) := by
  intro leaves r d output heap
  have live := (seeded_content oracle msg key).1
  have ready := seeded_tail_ready oracle msg key
  have entry := tail_entry leaves live
  have pairs := unit_pairs oracle msg r key _ ready
  obtain ⟨content,heapReg,outReg⟩ := tail_content oracle leaves entry heap (physical_heap_level21 oracle msg r)
    (physical_heap_240 oracle msg r) (physical_heap_238 oracle msg r) pairs
  exact k3_serialize _ heap (memoryView leaves) oracle d key _ (eval_tail oracle leaves) heapReg outReg content ready

theorem counted_commit (o : Oracle) (msg : Message) :
    o.run (actual.run .commit msg)=(do let k ← $ᵗ Key;return (packedOutput o (seededLeaves o msg k),commitCalls)) := by
  rw [commit_of_image actual exact_image.symm (by decide) msg ⟨rfl,rfl,rfl,rfl⟩]
  unfold commitTrace;rw [oracle_run_coins_bind];apply bind_congr;intro k
  rw [oracle_run_bind,fixed_scan_run _ _ _ _ (by decide),pure_bind];dsimp only
  rw [oracle_run_bind,show o.run (tailBody _)=_ from tail_counted o _,pure_bind]
  simp only [oracle_run_pure,pure_bind]
  simp only [packedOutput,seededLeaves];rfl

end TwoPermutationPrototype.Grouped
