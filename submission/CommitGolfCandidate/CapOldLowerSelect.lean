import CommitGolfCandidate.CapOldProofSlots
import CommitGolfCandidate.CapHonestLowerBytes
import CommitGolfCandidate.CapLowerSlotValue

/-! Select the first seventeen digest slots of each old opening record. The
equality is about bytes loaded from the same serialized trapdoor, and holds
without any honest-hash or collision assumption. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local irreducible] readBuffer

def capOldLowerBytes (positions : Positions) (proof : Proof) : Proof :=
  (List.ofFn (fun slot : Fin (17*positions.card) =>
    capOldProofSlot proof (slot.val/17) (slot.val%17))).flatten

theorem cap_old_lower_reference (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) :
    capOldLowerBytes positions (referenceOpening heap salt positions) =
      capDigestEncoding (List.ofFn (fun slot : Fin (17*positions.card) =>
        referenceOpeningDigest heap salt positions (slot.val/17) (slot.val%17))) := by
  unfold capOldLowerBytes capDigestEncoding
  rw [List.flatMap_def,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext slot
  exact cap_old_reference_slot heap salt positions (slot.val/17) (slot.val%17)
    (by have bounded := slot.isLt; omega) (by omega)

theorem cap_old_lower_loaded (message : Message) (committed : MachineState)
    (positions : Positions) :
    capOldLowerBytes positions
      (referenceOpening (heapDigest committed 4294971424)
        (fun index => readNonce committed (5368713248+24*index.val)) positions) =
      capDigestEncoding (capOpenLowerDigests
        (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor)
        positions) := by
  rw [cap_old_lower_reference]
  apply congrArg capDigestEncoding
  unfold capOpenLowerDigests
  apply congrArg List.ofFn
  funext slot
  have present : slot.val/17 < positions.card := by
    have bounded := slot.isLt
    omega
  have inside : slot.val%17 < 17 := Nat.mod_lt _ (by decide)
  let index : Index := (capOpenRequestedIndices positions)[slot.val/17]'(by
    simpa only [capOpenRequestedIndices,Finset.length_sort] using present)
  have selected : openingIndex positions (slot.val/17)=index.val := by
    simp only [openingIndex,dif_pos present,index,capOpenRequestedIndices]
  have loaded := cap_honest_lower_loaded_slot message committed positions
    index (slot.val%17) inside
  change _ = capLowerSlotPayload (slot.val%17) (readBuffer _
    (capLowerSlotAddress capOpenAbiRecordContext index.val (slot.val%17)) 32)
  rw [loaded]
  rw [cap_lower_slot_value _ _ inside]
  by_cases zero : slot.val%17=0
  · simp only [referenceOpeningDigest,if_pos zero,dif_pos zero,
      capHonestLowerRecord,selected]
  · simp only [referenceOpeningDigest,if_neg zero,dif_neg zero,
      capHonestLowerRecord,selected]

end CommitGolfCandidate
