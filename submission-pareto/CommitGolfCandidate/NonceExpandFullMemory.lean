import CommitGolfCandidate.NonceExpandSuffixMemory

/-! Composition of the first footer relocation with the following backward
record expansion. Every output word is tied to the original packed memory. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

structure NonceFullExpandMemory (base count words : Nat) (before after : MachineState) : Prop where
  copied : ∀ index < 68*count+words,
    after.getMem (address base index)=
      if index<68*count ∧ index%68=3 then 0 else before.getMem
        (address base (if index<68*count then nonceExpandedSourceWord index else index-count))
  frame : ∀ location, (∀ index < 68*count+words, location ≠ address base index) →
    after.getMem location=before.getMem location

theorem nonce_expand_source_bound (index count : Nat) (inside : index<68*count) :
    nonceExpandedSourceWord index<67*count := by
  have remainder:=Nat.mod_lt index (by decide : 0<68)
  have quotient:=Nat.mod_add_div index 68
  unfold nonceExpandedSourceWord
  split <;> omega

theorem nonce_expand_footer_records_memory (base count words : Nat)
    (before middle after : MachineState)
    (window : base+544*count+8*words ≤ MEMORY_BYTES)
    (footer : NonceWordMove (base+536*count) (base+544*count) words before middle)
    (recordsFrame : NonceExpandSuffixMemory base count 0 middle after) :
    NonceFullExpandMemory base count words before after := by
  constructor
  · intro index inside
    by_cases inPrefix : index<68*count
    · rw [if_pos inPrefix,recordsFrame.copied index (by omega) inPrefix]
      by_cases padding : index%68=3
      · simp only [padding,inPrefix,true_and,if_true]
      · simp only [padding,and_false,if_false]
        apply footer.frame
        intro current currentBound
        have sourceBound:=nonce_expand_source_bound index count inPrefix
        apply address_ne (by omega)
        norm_num [MEMORY_BYTES] at window
        omega
    · rw [if_neg inPrefix,if_neg (by simp only [inPrefix,false_and,not_false_eq_true])]
      rw [recordsFrame.frame]
      · have inFooter : index-68*count<words := by omega
        have destination : address base index=address (base+544*count) (index-68*count) := by
          unfold address; congr 1; omega
        rw [destination,footer.copied (index-68*count) inFooter]
        congr 1
        unfold address; congr 1; omega
      · intro previous lower upper
        apply Ne.symm
        apply address_ne (by omega)
        norm_num [MEMORY_BYTES] at window
        omega
  · intro location outside
    rw [recordsFrame.frame]
    · apply footer.frame
      intro index inside
      have destination : address (base+544*count) index=address base (68*count+index) := by
        unfold address; congr 1; omega
      rw [destination]
      exact outside _ (by omega)
    · intro index lower upper
      exact outside index (by omega)
end CommitGolfCandidate
