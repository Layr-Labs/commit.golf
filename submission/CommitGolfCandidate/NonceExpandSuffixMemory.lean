import CommitGolfCandidate.NonceExpandRecordMemory
import CommitGolfCandidate.NonceExpandOuter

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

def nonceExpandedSourceWord (index : Nat) : Nat :=
  67*(index/68)+(if index%68<3 then index%68 else index%68-1)

theorem nonce_expanded_source_record (record index : Nat) (inside : index<68) :
    nonceExpandedSourceWord (68*record+index)=
      67*record+(if index<3 then index else index-1) := by
  have quotient : (68*record+index)/68=record := by omega
  have remainder : (68*record+index)%68=index := by omega
  simp only [nonceExpandedSourceWord,quotient,remainder]

structure NonceExpandSuffixMemory (base count remaining : Nat)
    (reference state : MachineState) : Prop where
  copied : ∀ index, 68*remaining ≤ index → index<68*count →
    state.getMem (address base index)=if index%68=3 then 0 else
      reference.getMem (address base (nonceExpandedSourceWord index))
  frame : ∀ location, (∀ index, 68*remaining ≤ index → index<68*count →
      location ≠ address base index) → state.getMem location=reference.getMem location

theorem nonce_expand_suffix_initial (base count : Nat) (state : MachineState) :
    NonceExpandSuffixMemory base count count state state := by
  constructor
  · intro index lower upper; omega
  · intro location _; rfl

theorem nonce_expand_suffix_unread (base count remaining : Nat) (reference state : MachineState)
    (ready : NonceExpandOuterReady base count (remaining+1) state)
    (preserved : NonceExpandSuffixMemory base count (remaining+1) reference state)
    (index : Nat) (inside : index<67) :
    state.getMem (address (base+536*remaining) index)=
      reference.getMem (address (base+536*remaining) index) := by
  apply preserved.frame
  intro previous lower upper
  apply address_ne (by omega)
  have window:=ready.window
  norm_num [MEMORY_BYTES] at window
  omega

theorem nonce_expand_suffix_next (base count remaining : Nat) (reference state : MachineState)
    (ready : NonceExpandOuterReady base count (remaining+1) state)
    (preserved : NonceExpandSuffixMemory base count (remaining+1) reference state) :
    NonceExpandSuffixMemory base count remaining reference (nonceExpandRecordState state) := by
  have recordReady:=nonce_expand_outer_record_ready base count remaining state ready
  have effect:=nonce_expand_actual_record_memory base count (remaining+1) state recordReady
  simp only [Nat.add_sub_cancel] at effect
  have window:=ready.window
  have remainingLe:=ready.remaining_le
  constructor
  · intro index lower upper
    by_cases earlier : 68*(remaining+1) ≤ index
    · rw [effect.frame]
      · exact preserved.copied index earlier upper
      · intro current inside
        apply Ne.symm
        apply address_ne (by omega)
        norm_num [MEMORY_BYTES] at window
        omega
    · let localIndex:=index-68*remaining
      have localBound : localIndex<68 := by dsimp only [localIndex]; omega
      have indexEq : index=68*remaining+localIndex := by dsimp only [localIndex]; omega
      have destination : address base index=address (base+544*remaining) localIndex := by
        unfold address; congr 1; dsimp only [localIndex]; omega
      have remainder : index%68=localIndex := by omega
      rw [destination,effect.copied localIndex localBound,remainder]
      by_cases padding : localIndex=3
      · simp only [if_pos padding]
      · rw [if_neg padding,if_neg padding]
        have selected : (if localIndex<3 then localIndex else localIndex-1)<67 := by split <;> omega
        rw [nonce_expand_suffix_unread base count remaining reference state ready preserved _ selected]
        congr 1
        rw [indexEq,nonce_expanded_source_record _ _ localBound]
        unfold address; congr 1; split <;> omega
  · intro location outside
    rw [effect.frame]
    · apply preserved.frame
      intro index lower upper
      exact outside index (by omega) upper
    · intro index inside
      have destination : address (base+544*remaining) index=address base (68*remaining+index) := by
        unfold address; congr 1; omega
      rw [destination]
      exact outside _ (by omega) (by omega)

theorem nonce_expand_outer_memory (base count remaining : Nat) (state : MachineState)
    (ready : NonceExpandOuterReady base count remaining state) (reference : MachineState)
    (preserved : NonceExpandSuffixMemory base count remaining reference state) :
    NonceExpandSuffixMemory base count 0 reference (capCountedRun nonceExpandRecordState remaining state) := by
  have final:=cap_counted_run_ready nonceExpandRecordState
    (fun remaining current => NonceExpandOuterReady base count remaining current ∧
      NonceExpandSuffixMemory base count remaining reference current)
    (fun remaining current currentReady =>
      ⟨nonce_expand_outer_next base count remaining current currentReady.1,
       nonce_expand_suffix_next base count remaining reference current currentReady.1 currentReady.2⟩)
    remaining state ⟨ready,preserved⟩
  exact final.2
end CommitGolfCandidate
