import CommitGolfCandidate.QuartetConcrete
import CommitGolfCandidate.QuartetTransport
import CommitGolfCandidate.K3GQModel
import CommitGolfCandidate.TwoPermutationPackedParentMask

/-!
# The honest heap of the commit

`physicalHeap` is the transcript's upper heap: level-22 node `g` is the parity truncation of the
group call on quartet `g`'s payload; an internal node `n` keeps `nodeKeep n` of the compression of its
children: all 256 bits at level 21, the low 240 bits at levels 17..20, the low 238 bits at the root and
levels 1..16.
-/

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Sampling.Quartet (leafAt quartetPayload quartetLookup upperHeap upper_heap_parent upper_heap_leaf)
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def digestWords (v : BitVec 256) : Words 4 := fun k => v.extractLsb' (64*k.val) 64

def physicalHeap (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) :=
  let p := BiPermutation.equiv Block oracle.permutation
  upperHeap (quartetLookup p) oracle.compression (pinnedFullLeafDigests p msg salts)

theorem physical_heap_parent (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) (n : Nat)
    (hn : 0<n) (small : n<4194304) :
    physicalHeap oracle msg salts n=nodeKeep n (oracle.compression
      (physicalHeap oracle msg salts (2*n+1) ++ physicalHeap oracle msg salts (2*n))) := by
  unfold physicalHeap
  exact upper_heap_parent _ _ _ n hn small

theorem physical_heap_level21 (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) (U : Nat)
    (small : U<2097152) :
    physicalHeap oracle msg salts (2097152+U)=oracle.compression
      (physicalHeap oracle msg salts (4194304+(2*U+1)) ++ physicalHeap oracle msg salts (4194304+2*U)) := by
  have parent := (physical_heap_parent oracle msg salts (2097152+U) (by omega) (by omega)).trans
    (node_keep_full (node := 2097152+U) (by omega) _)
  rw [show 2*(2097152+U)+1=4194304+(2*U+1) by omega,show 2*(2097152+U)=4194304+2*U by omega] at parent
  exact parent

/-- Levels 17..20 (nodes `[2^17, 2^21)`) keep the low 240 bits of the compression. -/
theorem physical_heap_240 (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) (n : Nat)
    (lo : 131072≤n) (hi : n<2097152) :
    physicalHeap oracle msg salts n=projectReply (oracle.compression
      (physicalHeap oracle msg salts (2*n+1) ++ physicalHeap oracle msg salts (2*n))) := by
  exact (physical_heap_parent oracle msg salts n (by omega) (by omega)).trans
    (node_keep_240 (node := n) (by omega) (by omega) _)

/-- The root and levels 1..16 (nodes `[1, 2^17)`) keep the low 238 bits of the compression. -/
theorem physical_heap_238 (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) (n : Nat)
    (pos : 0<n) (hi : n<131072) :
    physicalHeap oracle msg salts n=pad238 (oracle.compression
      (physicalHeap oracle msg salts (2*n+1) ++ physicalHeap oracle msg salts (2*n))) := by
  exact (physical_heap_parent oracle msg salts n pos (by omega)).trans (node_keep_238 (node := n) (by omega) _)

theorem physical_heap_leaf (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) (g : Nat) (small : g<4194304) :
    physicalHeap oracle msg salts (4194304+g) =
      quartetNode g (oracle.permutation (quartetEncode (quartetPayload
        (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) msg salts) g))) := by
  unfold physicalHeap
  rw [upper_heap_leaf _ _ _ g small]
  rfl

end TwoPermutationPrototype.QuartetCommit
