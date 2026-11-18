import CommitGolfCandidate.QuartetConcrete
import CommitGolfCandidate.QuartetCommitQFrame
import CommitGolfCandidate.TwoPermutationPackedParentMask
import CommitGolfCandidate.TwoPermutationBindingLeaf

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Sampling.Quartet (leafAt quartetPayload quartetLookup upperHeap)
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def digestWords (v : BitVec 256) : Words 4 := fun k => v.extractLsb' (64*k.val) 64

private theorem all_bits (l r : BitVec 1600) (same : ∀ k : Fin 25, l.extractLsb' (64*k.val) 64=r.extractLsb' (64*k.val) 64) : l=r := by
  apply BitVec.eq_of_getLsbD_eq;intro b hb
  have eq:=congrArg (fun v : BitVec 64 => v.getLsbD (b%64)) (same ⟨b/64,by omega⟩)
  simpa only [Fin.val_mk,BitVec.getLsbD_extractLsb',show b%64<64 by omega,decide_true,Bool.true_and,
    show 64*(b/64)+b%64=b by omega] using eq

private theorem packet_word (d : Nat → BitVec 256) (g : Nat) (k : Fin 25) :
    quadWords (fun i => digestWords (d i)) g k =
      ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' (64*k.val) 64 := by
  fin_cases k
  · change (0 : Word) = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 0 64
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64≤576)]
    rfl
  · change (0 : Word) = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 64 64
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 64+64≤576)]
    rfl
  · change (0 : Word) = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 128 64
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 128+64≤576)]
    rfl
  · change (0 : Word) = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 192 64
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 192+64≤576)]
    rfl
  · change (0 : Word) = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 256 64
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 256+64≤576)]
    rfl
  · change (0 : Word) = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 320 64
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 320+64≤576)]
    rfl
  · change (0 : Word) = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 384 64
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 384+64≤576)]
    rfl
  · change (0 : Word) = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 448 64
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 448+64≤576)]
    rfl
  · change (0 : Word) = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 512 64
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 512+64≤576)]
    rfl
  · change (d (4*g+0)).extractLsb' 0 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 576 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤576)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64≤256)]
    try rfl
  · change (d (4*g+0)).extractLsb' 64 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 640 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤640)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 64+64≤256)]
    try rfl
  · change (d (4*g+0)).extractLsb' 128 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 704 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤704)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 128+64≤256)]
    try rfl
  · change (d (4*g+0)).extractLsb' 192 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 768 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤768)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 192+64≤256)]
    try rfl
  · change (d (4*g+1)).extractLsb' 0 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 832 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤832)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤256)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64≤256)]
    try rfl
  · change (d (4*g+1)).extractLsb' 64 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 896 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤896)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤320)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 64+64≤256)]
    try rfl
  · change (d (4*g+1)).extractLsb' 128 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 960 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤960)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤384)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 128+64≤256)]
    try rfl
  · change (d (4*g+1)).extractLsb' 192 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 1024 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤1024)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤448)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 192+64≤256)]
    try rfl
  · change (d (4*g+2)).extractLsb' 0 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 1088 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤1088)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤512)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤256)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64≤256)]
    try rfl
  · change (d (4*g+2)).extractLsb' 64 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 1152 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤1152)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤576)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤320)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 64+64≤256)]
    try rfl
  · change (d (4*g+2)).extractLsb' 128 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 1216 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤1216)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤640)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤384)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 128+64≤256)]
    try rfl
  · change (d (4*g+2)).extractLsb' 192 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 1280 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤1280)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤704)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤448)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 192+64≤256)]
    try rfl
  · change (d (4*g+3)).extractLsb' 0 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 1344 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤1344)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤768)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤512)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤256)]
    try simp only [Nat.reduceSub]
    try rfl
  · change (d (4*g+3)).extractLsb' 64 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 1408 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤1408)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤832)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤576)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤320)]
    try simp only [Nat.reduceSub]
    try rfl
  · change (d (4*g+3)).extractLsb' 128 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 1472 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤1472)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤896)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤640)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤384)]
    try simp only [Nat.reduceSub]
    try rfl
  · change (d (4*g+3)).extractLsb' 192 64 = ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)).extractLsb' 1536 64
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 576≤1536)]
    simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤960)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤704)]
    try simp only [Nat.reduceSub]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256≤448)]
    try simp only [Nat.reduceSub]
    try rfl

theorem packing_exact (d : Nat → BitVec 256) (g : Nat) :
    packBuffer (quadWords (fun i => digestWords (d i)) g) =
      ((d (4*g+3) ++ d (4*g+2) ++ d (4*g+1) ++ d (4*g)) ++ (0 : BitVec 576)) := by
  apply all_bits;intro k;exact (packed_word _ k).trans (packet_word d g k)

def physicalHeap (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) :=
  let p := BiPermutation.equiv Block oracle.permutation
  upperHeap (quartetLookup p) oracle.compression (pinnedFullLeafDigests p msg salts)

theorem physical_heap_parent (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) (n : Nat)
    (hn : 0<n) (small : n<4194304) :
    physicalHeap oracle msg salts n=projectReply (oracle.compression (physicalHeap oracle msg salts (2*n+1) ++ physicalHeap oracle msg salts (2*n))) := by
  unfold physicalHeap upperHeap
  rw [reference_heap_parent _ _ _ _ hn small];rfl

theorem physical_heap_leaf (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) (g : Nat) (small : g<4194304) :
    let d := leafAt (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) msg salts)
    physicalHeap oracle msg salts (4194304+g) = outputDigest (quadReply oracle (fun i => digestWords (d i)) g) := by
  dsimp only;unfold physicalHeap upperHeap quadReply
  rw [reference_heap_leaf _ _ _ _ small,packing_exact]
  rfl
end TwoPermutationPrototype.QuartetCommit

#print axioms TwoPermutationPrototype.QuartetCommit.packing_exact
