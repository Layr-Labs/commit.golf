import CommitGolfCandidate.NonceCompactWhole
import CommitGolfCandidate.NonceMemoryBytes

/-! Byte-list semantics of the compaction: the delivered bytes are `s6Pack` of the internal proof,
for arbitrary contents of the internal proof. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_compacted_bytes (orig final : MachineState) (base count nodes : Nat)
    (done : NonceCompacted orig base count (560 * count + 32 * nodes) final) :
    nonceMemoryBytes final base (560 * count + 32 * nodes) =
      s6Pack count (nonceMemoryBytes orig base (576 * count + 32 * nodes)) := by
  have size := nonce_memory_bytes_length orig base (576 * count + 32 * nodes)
  apply List.ext_getElem
  · rw [nonce_memory_bytes_length, s6_pack_length count nodes _ size]
  · intro k left right
    have inside : k < 560 * count + 32 * nodes := by rwa [nonce_memory_bytes_length] at left
    have selected := s6_pack_getElem? count nodes _ size k inside
    rw [List.getElem?_eq_getElem right] at selected
    have bounded : s6PackSource count k < 576 * count + 32 * nodes := by
      by_contra outside
      rw [List.getElem?_eq_none (by rw [size]; omega)] at selected
      contradiction
    have source : (nonceMemoryBytes orig base (576 * count + 32 * nodes))[s6PackSource count k]? =
        some (orig.getByte (BitVec.ofNat 64 (base + s6PackSource count k))) := by
      simp only [nonceMemoryBytes, List.getElem?_map, List.getElem?_range bounded, Option.map_some]
    have value := Option.some.inj (selected.trans source)
    rw [value]
    simp only [nonceMemoryBytes, List.getElem_map, List.getElem_range]
    exact done.packed k inside

end CommitGolfCandidate
