import CommitGolfCandidate.NonceActualRecordMemory
import CommitGolfCandidate.NonceCompactOuter

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def noncePackedSourceWord (index : Nat) : Nat :=
  68*(index/67)+(if index%67<3 then index%67 else index%67+1)

theorem nonce_packed_source_record (record index : Nat) (inside : index<67) :
    noncePackedSourceWord (67*record+index)=
      68*record+(if index<3 then index else index+1) := by
  have quotient : (67*record+index)/67=record := by omega
  have remainder : (67*record+index)%67=index := by omega
  simp only [noncePackedSourceWord, quotient, remainder]

structure NonceCompactPrefixMemory (base count remaining : Nat)
    (reference state : MachineState) : Prop where
  copied : ∀ index < 67*(count-remaining),
    state.getMem (address base index)=reference.getMem (address base (noncePackedSourceWord index))
  frame : ∀ location, (∀ index < 67*(count-remaining), location ≠ address base index) →
    state.getMem location=reference.getMem location

theorem nonce_compact_prefix_initial (base count : Nat) (state : MachineState) :
    NonceCompactPrefixMemory base count count state state := by
  constructor
  · intro index inside
    omega
  · intro location _
    rfl

theorem nonce_compact_prefix_unread (base count remaining : Nat)
    (reference state : MachineState)
    (ready : NonceCompactOuterReady base count (remaining+1) state)
    (preserved : NonceCompactPrefixMemory base count (remaining+1) reference state)
    (index : Nat) (inside : index<68) :
    state.getMem (address (base+544*(count-(remaining+1))) index)=
      reference.getMem (address (base+544*(count-(remaining+1))) index) := by
  apply preserved.frame
  intro previous earlier
  apply Ne.symm
  apply address_ne (by omega)
  have window:=ready.window
  have remainingLe:=ready.remaining_le
  norm_num [MEMORY_BYTES] at window
  omega

theorem nonce_compact_prefix_next (base count remaining : Nat)
    (reference state : MachineState)
    (ready : NonceCompactOuterReady base count (remaining+1) state)
    (preserved : NonceCompactPrefixMemory base count (remaining+1) reference state) :
    NonceCompactPrefixMemory base count remaining reference (nonceCompactRecordState state) := by
  have recordReady:=nonce_compact_outer_record_ready base count remaining state ready
  have effect:=nonce_compact_actual_record_memory base count (remaining+1) state recordReady
  have remainingLe:=ready.remaining_le
  have window:=ready.window
  have progress : count-remaining=count-(remaining+1)+1 := by omega
  constructor
  · intro index inside
    by_cases earlier : index<67*(count-(remaining+1))
    · rw [effect.frame]
      · exact preserved.copied index earlier
      · intro current currentBound
        apply address_ne (by omega)
        norm_num [MEMORY_BYTES] at window
        omega
    · let localIndex := index-67*(count-(remaining+1))
      have localBound : localIndex<67 := by dsimp only [localIndex]; omega
      have destination : address base index=
          address (base+536*(count-(remaining+1))) localIndex := by
        unfold address
        congr 1
        dsimp only [localIndex]
        omega
      rw [destination, effect.copied localIndex localBound]
      have selected : (if localIndex<3 then localIndex else localIndex+1)<68 := by
        split <;> omega
      rw [nonce_compact_prefix_unread base count remaining reference state ready preserved _ selected]
      have indexEq : index=67*(count-(remaining+1))+localIndex := by
        dsimp only [localIndex]
        omega
      congr 1
      rw [indexEq, nonce_packed_source_record _ _ localBound]
      unfold address
      congr 1
      split <;> omega
  · intro location outside
    rw [effect.frame]
    · apply preserved.frame
      intro index inside
      exact outside index (by omega)
    · intro index inside
      have destination : address (base+536*(count-(remaining+1))) index=
          address base (67*(count-(remaining+1))+index) := by
        unfold address
        congr 1
        omega
      rw [destination]
      exact outside _ (by omega)

theorem nonce_compact_outer_memory (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactOuterReady base count remaining state)
    (reference : MachineState)
    (preserved : NonceCompactPrefixMemory base count remaining reference state) :
    NonceCompactPrefixMemory base count 0 reference
      (capCountedRun nonceCompactRecordState remaining state) := by
  have final:=cap_counted_run_ready nonceCompactRecordState
    (fun remaining current => NonceCompactOuterReady base count remaining current ∧
      NonceCompactPrefixMemory base count remaining reference current)
    (fun remaining current currentReady =>
      ⟨nonce_compact_outer_next base count remaining current currentReady.1,
       nonce_compact_prefix_next base count remaining reference current currentReady.1 currentReady.2⟩)
    remaining state ⟨ready,preserved⟩
  exact final.2

end CommitGolfCandidate
