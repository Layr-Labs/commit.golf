import CommitGolfCandidate.CapOpenSlots
import CommitGolfCandidate.CapByteSlots
import CommitGolfCandidate.CapHeapView

/-! Actual emitted digest slots give the exact header-free cap bytes. The heap
and mark equations here concern the original machine memory; deriving them
from an honest commitment and the populated record pass is still separate. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_slots_encoding (state : MachineState) (base : Nat)
    (digests : List Digest)
    (slots : ∀ ordinal (present : ordinal < digests.length),
      readBuffer state (base + 32*ordinal) 32 = digests[ordinal])
    (offset : Nat) (inside : offset < 32*digests.length) :
    state.getByte (BitVec.ofNat 64 (base+offset)) =
      (capDigestEncoding digests)[offset]?.getD 0 := by
  have present : offset / 32 < digests.length := by omega
  have small : offset % 32 < 32 := Nat.mod_lt _ (by decide)
  have decomp : 32*(offset/32) + offset%32 = offset := by omega
  have byteRead := read_buffer_byte state (base + 32*(offset/32)) 32 (offset%32) small
  rw [slots (offset/32) present] at byteRead
  have encoded := cap_encoding_byte digests [] (offset/32) (offset%32) present small
  have address : base + 32*(offset/32) + offset%32 = base+offset := by omega
  rw [address] at byteRead
  exact byteRead.symm.trans (by simpa only [List.append_nil, decomp] using encoded.symm)

theorem cap_open_run_bytes (marked : Nat → Bool)
    (rootBase limit floor : Nat) (reference : MachineState)
    (limitBound : limit ≤ MEMORY_BYTES)
    (rootBound : rootBase + 8192 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (heapBelow : rootBase + 8192 ≤ floor)
    (count : Nat) (control : CapDfsControl) (state final : MachineState)
    (ready : CapOpenReadReady marked rootBase limit floor reference control state)
    (reached : final ∈ support (capDfsRun false marked count control state))
    (offset : Nat)
    (inside : offset < 32*(capControlBoundaries marked count control).length) :
    final.getByte (BitVec.ofNat 64 ((state.getReg .x25).toNat + offset)) =
      (capDigestEncoding ((capControlBoundaries marked count control).map
        (fun node => readBuffer reference (rootBase+32*node) 32)))[offset]?.getD 0 := by
  apply cap_slots_encoding final (state.getReg .x25).toNat _ ?_ offset
    (by simpa only [List.length_map] using inside)
  intro ordinal present
  have inNodes : ordinal < (capControlBoundaries marked count control).length :=
    by simpa only [List.length_map] using present
  simpa only [List.getElem_map] using
    cap_open_run_slots marked rootBase limit floor reference limitBound rootBound
      rootAligned heapBelow count control state final ready reached ordinal
      (capControlBoundaries marked count control)[ordinal]
      (List.getElem?_eq_getElem inNodes)

theorem cap_open_canonical_bytes (compress : Compression) (marked : Nat → Bool)
    (rootBase limit floor : Nat) (reference : MachineState)
    (limitBound : limit ≤ MEMORY_BYTES)
    (rootBound : rootBase + 8192 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (heapBelow : rootBase + 8192 ≤ floor)
    (hashParents : ∀ node, 0 < node → node < 128 →
      readBuffer reference (rootBase+32*node) 32 =
        combine compress (readBuffer reference (rootBase+32*(2*node)) 32)
          (readBuffer reference (rootBase+32*(2*node+1)) 32))
    (markParents : ∀ node, 0 < node → node < 128 →
      marked node = (marked (2*node) || marked (2*node+1)))
    (state final : MachineState)
    (ready : CapOpenReadReady marked rootBase limit floor reference (.visit 1) state)
    (reached : final ∈ support (capDfsRun false marked 510 (.visit 1) state))
    (offset : Nat)
    (inside : offset < (capDigestEncoding
      (capProof compress
        (capHeapTree (fun node => readBuffer reference (rootBase+32*node) 32) 7 1)
        (capHeapView (fun node => readBuffer reference (rootBase+32*node) 32)
          marked 7 1))).length) :
    final.getByte (BitVec.ofNat 64 ((state.getReg .x25).toNat + offset)) =
      (capDigestEncoding (capProof compress
        (capHeapTree (fun node => readBuffer reference (rootBase+32*node) 32) 7 1)
        (capHeapView (fun node => readBuffer reference (rootBase+32*node) 32)
          marked 7 1)))[offset]?.getD 0 := by
  have serialization := cap_heap_serialization compress
    (fun node => readBuffer reference (rootBase+32*node) 32) marked hashParents markParents
  rw [← serialization] at inside ⊢
  rw [cap_digest_encoding_length, List.length_map] at inside
  exact cap_open_run_bytes marked rootBase limit floor reference limitBound rootBound
    rootAligned heapBelow 510 (.visit 1) state final ready reached offset inside

end CommitGolfCandidate
