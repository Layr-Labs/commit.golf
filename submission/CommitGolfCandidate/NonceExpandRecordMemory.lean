import CommitGolfCandidate.NonceExpandMemory
import CommitGolfCandidate.NonceExpandReady

/-! One expanded record consists of three original nonce words, one inserted
zero word and sixty-four original sibling words. The three concrete memory
operations are composed with a frame for every other word address. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

structure NonceRecordExpandMove (source target : Nat) (before after : MachineState) : Prop where
  copied : ∀ index < 68,
    after.getMem (address target index)=if index=3 then 0 else
      before.getMem (address source (if index<3 then index else index-1))
  frame : ∀ location, (∀ index < 68, location ≠ address target index) →
    after.getMem location=before.getMem location

private theorem sibling_destination (base index : Nat) :
    address (base+32) index=address base (index+4) := by
  unfold address
  congr 1
  omega

private theorem sibling_source (base index : Nat) :
    address (base+24) index=address base (index+3) := by
  unfold address
  congr 1
  omega

theorem nonce_expand_moves_compose (source target : Nat) (before middle padded after : MachineState)
    (ordered : source ≤ target) (sourceWindow : source+536 ≤ MEMORY_BYTES)
    (targetWindow : target+544 ≤ MEMORY_BYTES)
    (siblings : NonceWordMove (source+24) (target+32) 64 before middle)
    (padding : padded.mem=(middle.setMem (address target 3) 0).mem)
    (nonce : NonceWordMove source target 3 padded after) : NonceRecordExpandMove source target before after := by
  have paddedWord (location : Word) : padded.getMem location=(middle.setMem (address target 3) 0).getMem location :=
    congrArg (fun memory : Word → Word => memory location) padding
  constructor
  · intro index inside
    by_cases inNonce : index<3
    · rw [if_neg (by omega : index ≠ 3),if_pos inNonce,nonce.copied index inNonce,
        paddedWord (address source index)]
      have different : address source index ≠ address target 3 :=
        address_ne (left:=source+8*index) (right:=target+8*3) (by omega)
          (address_small target 68 3 (by omega) (by decide))
      rw [MachineState.getMem_setMem_ne different]
      apply siblings.frame
      intro sibling siblingBound
      exact address_ne (by omega)
        (address_small (target+32) 64 sibling (by omega) siblingBound)
    · by_cases isPadding : index=3
      · subst index
        rw [if_pos rfl,nonce.frame]
        · rw [paddedWord (address target 3),MachineState.getMem_setMem_eq]
        · intro earlier earlierBound
          exact Ne.symm (address_ne (by omega) (address_small target 68 3 (by omega) (by decide)))
      · rw [if_neg isPadding,if_neg inNonce,nonce.frame]
        · have different : address target index ≠ address target 3 :=
            Ne.symm (address_ne (left:=target+8*3) (right:=target+8*index) (by omega)
              (address_small target 68 index (by omega) inside))
          rw [paddedWord (address target index),MachineState.getMem_setMem_ne different]
          have destination : address target index=address (target+32) (index-4) := by
            rw [sibling_destination]
            congr 1
            omega
          rw [destination,siblings.copied (index-4) (by omega),sibling_source]
          congr 1
          congr 1
          omega
        · intro earlier earlierBound
          exact Ne.symm (address_ne (by omega) (address_small target 68 index (by omega) inside))
  · intro location outside
    rw [nonce.frame]
    · rw [paddedWord location,MachineState.getMem_setMem_ne (outside 3 (by decide))]
      apply siblings.frame
      intro index inside
      rw [sibling_destination]
      exact outside (index+4) (by omega)
    · intro index inside
      exact outside index (by omega)

theorem nonce_record_expand_transfer (source target : Nat) (before after before' after' : MachineState)
    (effect : NonceRecordExpandMove source target before after)
    (first : before.mem=before'.mem) (last : after.mem=after'.mem) :
    NonceRecordExpandMove source target before' after' := by
  constructor
  · intro index inside
    simpa only [MachineState.getMem,first,last] using effect.copied index inside
  · intro location outside
    simpa only [MachineState.getMem,first,last] using effect.frame location outside

theorem nonce_expand_actual_record_memory (base count remaining : Nat) (state : MachineState)
    (ready : NonceExpandRecordReady base count remaining state) :
    NonceRecordExpandMove (base+536*(remaining-1)) (base+544*(remaining-1)) state (nonceExpandRecordState state) := by
  have siblingsReady:=nonce_expand_siblings_ready base count remaining state ready
  have nonceReady:=nonce_expand_nonce_ready base count remaining state ready
  have moves:=nonce_expand_record_moves state _ _ siblingsReady nonceReady
  have window:=ready.window
  have remainingLe:=ready.remaining_le
  have positive:=ready.positive
  have composed:=nonce_expand_moves_compose (base+536*(remaining-1)) (base+544*(remaining-1))
    state (nonceExpandSiblingsCopied state) (nonceExpandPaddingState state) (nonceExpandNonceCopied state)
    (by omega) (by omega) (by omega) moves.1 moves.2.1 moves.2.2.1
  exact nonce_record_expand_transfer _ _ state (nonceExpandNonceCopied state) state (nonceExpandRecordState state)
    composed rfl moves.2.2.2.symm

end CommitGolfCandidate
