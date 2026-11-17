import CommitGolfCandidate.NonceCompactMemory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

structure NonceRecordMove (source target : Nat) (before after : MachineState) : Prop where
  copied : ∀ index < 67,
    after.getMem (address target index)=
      before.getMem (address source (if index<3 then index else index+1))
  frame : ∀ location, (∀ index < 67, location ≠ address target index) →
    after.getMem location=before.getMem location

private theorem sibling_address (base index : Nat) :
    address (base+24) index=address base (index+3) := by
  unfold address
  congr 1
  omega

private theorem sibling_source (base index : Nat) :
    address (base+32) index=address base (index+4) := by
  unfold address
  congr 1
  omega

theorem nonce_record_moves_compose (source target : Nat) (before middle after : MachineState)
    (ordered : target ≤ source) (sourceWindow : source+544 ≤ MEMORY_BYTES)
    (targetWindow : target+536 ≤ MEMORY_BYTES)
    (nonce : NonceWordMove source target 3 before middle)
    (siblings : NonceWordMove (source+32) (target+24) 64 middle after) :
    NonceRecordMove source target before after := by
  constructor
  · intro index inside
    by_cases inNonce : index<3
    · rw [if_pos inNonce]
      rw [siblings.frame]
      · exact nonce.copied index inNonce
      · intro sibling siblingBound
        rw [sibling_address]
        exact address_ne (by omega)
          (address_small target 67 (sibling+3) (by omega) (by omega))
    · rw [if_neg inNonce]
      have inSiblings : index-3<64 := by omega
      have destination : address target index=address (target+24) (index-3) := by
        rw [sibling_address]
        congr 1
        omega
      rw [destination, siblings.copied (index-3) inSiblings]
      rw [nonce.frame]
      · congr 1
        rw [sibling_source]
        congr 1
        omega
      · intro previous previousBound
        apply Ne.symm
        apply address_ne (by omega)
        have sourceBound : source+32+8*(index-3)<2^64 := by
          norm_num [MEMORY_BYTES] at sourceWindow
          omega
        exact sourceBound
  · intro location outside
    rw [siblings.frame]
    · exact nonce.frame location (fun index inside => outside index (by omega))
    · intro index inside
      rw [sibling_address]
      exact outside (index+3) (by omega)

end CommitGolfCandidate
