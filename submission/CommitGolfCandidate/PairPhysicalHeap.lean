import CommitGolfCandidate.QuartetWordBridge
import CommitGolfCandidate.PairLeafModel

/-! Pair-heads analog of `physicalHeap` / `originalLeaf`: the Quartet heap and leaf digests over `pairFullLeafDigests`. -/
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Sampling.Quartet (leafAt quartetPayload quartetLookup upperHeap)

def pairLeaf (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) :=
  leafAt (pairFullLeafDigests (BiPermutation.equiv Block oracle.permutation) msg salts)

def pairHeap (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) :=
  let p := BiPermutation.equiv Block oracle.permutation
  upperHeap (quartetLookup p) oracle.compression (pairFullLeafDigests p msg salts)

theorem pair_heap_parent (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) (n : Nat)
    (hn : 0<n) (small : n<4194304) :
    pairHeap oracle msg salts n=projectReply (oracle.compression (pairHeap oracle msg salts (2*n+1) ++ pairHeap oracle msg salts (2*n))) := by
  unfold pairHeap upperHeap
  rw [reference_heap_parent _ _ _ _ hn small];rfl

theorem pair_heap_leaf (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) (g : Nat) (small : g<4194304) :
    pairHeap oracle msg salts (4194304+g) = outputDigest (quadReply oracle (fun i => digestWords (pairLeaf oracle msg salts i)) g) := by
  unfold pairHeap upperHeap quadReply pairLeaf
  rw [reference_heap_leaf _ _ _ _ small,packing_exact]
  rfl

end TwoPermutationPrototype.QuartetCommit
