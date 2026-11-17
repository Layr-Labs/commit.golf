import CommitGolfCandidate.HidingMachine
import CommitGolfCandidate.CapEncoding

/-! Pure byte selection from a full-path opening. Every selected slot consists
of its original thirty-two bytes, with no hash evaluation or oracle call.
Out-of-range inputs are total; only valid honest slots are identified below. -/
namespace CommitGolfCandidate
open CommitGolf
set_option autoImplicit false
set_option maxHeartbeats 200000

def capOldProofSlot (proof : Proof) (ordinal part : Nat) : Proof :=
  List.ofFn (fun offset : Fin 32 =>
    proof[800*ordinal+32*part+offset.val]?.getD 0)

theorem cap_old_reference_slot (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) (ordinal part : Nat)
    (present : ordinal < positions.card) (inside : part < 25) :
    capOldProofSlot (referenceOpening heap salt positions) ordinal part =
      digestBytes (referenceOpeningDigest heap salt positions ordinal part) := by
  unfold capOldProofSlot digestBytes
  apply congrArg List.ofFn
  funext offset
  have byteBound : 800*ordinal+32*part+offset.val <
      (referenceOpening heap salt positions).length := by
    rw [reference_opening_length]
    omega
  rw [List.getElem?_eq_getElem byteBound,Option.getD_some]
  have record : (800*ordinal+32*part+offset.val)/800=ordinal := by omega
  have within : (800*ordinal+32*part+offset.val)%800=32*part+offset.val := by omega
  have slot : (32*part+offset.val)/32=part := by omega
  have byte : (800*ordinal+32*part+offset.val)%32=offset.val := by omega
  simp only [referenceOpening,List.getElem_map,List.getElem_range,
    record,within,slot,byte]

end CommitGolfCandidate
