import CommitGolfCandidate.CapOpenLoadedRecordSlots
import CommitGolfCandidate.CapOpenEncoding

/-! Exact header-free lower-record bytes from original ABI heap/salt slots.
Flattening eighteen slots per ordinal gives the same machine addresses; empty
requests have an empty list. Honest hash/tree semantics are not assumed here. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenLowerDigests
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : List Digest :=
  List.ofFn (fun slot : Fin (18*positions.card) =>
    readBuffer (capProgram.initialState .opening (trapdoor, positions))
      (capLowerSlotAddress capOpenAbiRecordContext
        ((capOpenRequestedIndices positions)[slot.val/18]'(by
          have bounded := slot.isLt
          simp only [capOpenRequestedIndices, Finset.length_sort]
          omega)).val (slot.val%18)) 32)

theorem cap_open_lower_digests_length
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (capOpenLowerDigests trapdoor positions).length = 18*positions.card := by
  simp only [capOpenLowerDigests, List.length_ofFn]

theorem cap_open_lower_digest_slots
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (slot : Nat)
    (inside : slot < (capOpenLowerDigests trapdoor positions).length) :
    readBuffer (capOpenRecordsFinal trapdoor positions)
      (capProgram.layout.proof+32*slot) 32 =
      (capOpenLowerDigests trapdoor positions)[slot] := by
  have bounded : slot < 18*positions.card := by
    simpa only [cap_open_lower_digests_length] using inside
  have ordinal : slot/18 < positions.card := by omega
  have within : slot%18 < 18 := Nat.mod_lt _ (by decide)
  have address : capProgram.layout.proof+32*slot =
      capProgram.layout.proof+576*(slot/18)+32*(slot%18) := by omega
  rw [address]
  simpa only [capOpenLowerDigests, List.getElem_ofFn] using
    cap_open_loaded_record_slot trapdoor positions positive (slot/18) ordinal
      (slot%18) within

theorem cap_open_lower_bytes
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (offset : Nat) (inside : offset < 576*positions.card) :
    (capOpenRecordsFinal trapdoor positions).getByte
        (BitVec.ofNat 64 (capProgram.layout.proof+offset)) =
      (capDigestEncoding (capOpenLowerDigests trapdoor positions))[offset]?.getD 0 := by
  exact cap_slots_encoding _ _ _ (cap_open_lower_digest_slots trapdoor positions positive)
    offset (by rw [cap_open_lower_digests_length]; omega)

end CommitGolfCandidate
