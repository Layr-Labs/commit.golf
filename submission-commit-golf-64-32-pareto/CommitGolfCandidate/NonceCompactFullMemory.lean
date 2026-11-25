import CommitGolfCandidate.NonceCompactPrefixMemory

/-! Appending the final forward footer move to the compacted lower records.
All packed words and the suffix are read from the original memory snapshot;
the copy overlap is handled by the already checked copy-loop invariant. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

structure NonceFullCompactMemory (base count words : Nat) (before after : MachineState) : Prop where
  copied : ∀ index < 67*count+words,
    after.getMem (address base index)=before.getMem
      (address base (if index<67*count then noncePackedSourceWord index else index+count))
  frame : ∀ location, (∀ index < 67*count+words, location ≠ address base index) →
    after.getMem location=before.getMem location

private theorem footer_address (base count index : Nat) :
    address (base+536*count) index=address base (67*count+index) := by
  unfold address
  congr 1
  omega

theorem nonce_compact_prefix_footer_memory (base count words : Nat)
    (before middle after : MachineState)
    (window : base+544*count+8*words ≤ MEMORY_BYTES)
    (recordsFrame : NonceCompactPrefixMemory base count 0 before middle)
    (footer : NonceWordMove (base+544*count) (base+536*count) words middle after) :
    NonceFullCompactMemory base count words before after := by
  constructor
  · intro index inside
    by_cases inPrefix : index<67*count
    · rw [if_pos inPrefix, footer.frame]
      · exact recordsFrame.copied index (by simpa using inPrefix)
      · intro current currentBound
        apply address_ne (by omega)
        norm_num [MEMORY_BYTES] at window
        omega
    · rw [if_neg inPrefix]
      have inFooter : index-67*count<words := by omega
      have destination : address base index=
          address (base+536*count) (index-67*count) := by
        rw [footer_address]
        congr 1
        omega
      rw [destination, footer.copied (index-67*count) inFooter, recordsFrame.frame]
      · congr 1
        unfold address
        congr 1
        omega
      · intro previous previousBound
        apply Ne.symm
        apply address_ne (by omega)
        norm_num [MEMORY_BYTES] at window
        omega
  · intro location outside
    rw [footer.frame]
    · apply recordsFrame.frame
      intro index inside
      exact outside index (by omega)
    · intro index inside
      rw [footer_address]
      exact outside _ (by omega)

end CommitGolfCandidate
