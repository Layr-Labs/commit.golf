import CommitGolfCandidate.CapCheckKnownRootFrame
import CommitGolfCandidate.CapCheckSuffixWords

/-! Remaining cap words and the unrounded byte tail at a reached checker state.
The tail is retained even when no full digest remains. Guard rejection and
final exact exhaustion are distinct predicates with their actual ordering. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] readBuffer

structure CapCheckWordSuffix (state : MachineState) (cursor : Nat)
    (words : List Digest) (tailBytes : Nat) : Prop where
  pointer : state.getReg .x25=BitVec.ofNat 64 cursor
  endPointer : state.getReg .x22=BitVec.ofNat 64 (cursor+32*words.length+tailBytes)
  high : 32768≤cursor
  bound : cursor+32*words.length+tailBytes≤MEMORY_BYTES
  partialBound : tailBytes<32
  slots : ∀ ordinal, (present : ordinal<words.length) →
    readBuffer state (cursor+32*ordinal) 32=words[ordinal]

theorem cap_check_word_suffix_small (state : MachineState) (cursor : Nat)
    (words : List Digest) (tailBytes : Nat)
    (suffix : CapCheckWordSuffix state cursor words tailBytes) :
    cursor<2^64 ∧ cursor+32*words.length+tailBytes<2^64 := by
  have bound := suffix.bound
  simp only [MEMORY_BYTES] at bound
  constructor <;> omega

theorem cap_check_word_suffix_short (marked : Nat → Bool) (node : Nat)
    (state : MachineState) (cursor : Nat) (words : List Digest) (tailBytes : Nat)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (absent : marked node=false) :
    capCheckDfsShort marked (.visit node) state=decide (words=[]) := by
  have small := cap_check_word_suffix_small state cursor words tailBytes suffix
  simp only [capCheckDfsShort,absent,Bool.false_eq_true,↓reduceIte,
    suffix.pointer,suffix.endPointer,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small.1,Nat.mod_eq_of_lt small.2]
  rw [decide_eq_decide]
  have tail := suffix.partialBound
  rw [←List.length_eq_zero_iff]
  omega

theorem cap_check_word_suffix_exhausted (state : MachineState) (cursor : Nat)
    (words : List Digest) (tailBytes : Nat)
    (suffix : CapCheckWordSuffix state cursor words tailBytes) :
    state.getReg .x25=state.getReg .x22 ↔ words=[] ∧ tailBytes=0 := by
  have small := cap_check_word_suffix_small state cursor words tailBytes suffix
  constructor
  · intro equal
    rw [suffix.pointer,suffix.endPointer] at equal
    have numeric := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small.1,
      Nat.mod_eq_of_lt small.2] at numeric
    rw [←List.length_eq_zero_iff]
    omega
  · rintro ⟨rfl,rfl⟩
    simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero] using
      suffix.pointer.trans suffix.endPointer.symm

/-- Consuming one complete word preserves every later word under the low-write
frame. This generic transport is instantiated only after the actual guard. -/
theorem cap_check_word_suffix_tail (state next : MachineState)
    (cursor : Nat) (head : Digest) (words : List Digest) (tailBytes : Nat)
    (suffix : CapCheckWordSuffix state cursor (head::words) tailBytes)
    (frame : CapHighBytes next state)
    (pointer : next.getReg .x25=BitVec.ofNat 64 (cursor+32))
    (endPointer : next.getReg .x22=state.getReg .x22) :
    CapCheckWordSuffix next (cursor+32) words tailBytes := by
  have address : cursor+32+32*words.length+tailBytes=
      cursor+32*(head::words).length+tailBytes := by simp only [List.length_cons]; omega
  refine ⟨pointer,?_,by have high := suffix.high; omega,?_,suffix.partialBound,?_⟩
  · rw [endPointer,suffix.endPointer,address]
  · rw [address]
    exact suffix.bound
  · intro ordinal present
    have oldPresent : ordinal+1<(head::words).length := by
      simp only [List.length_cons]; omega
    have slot := suffix.slots (ordinal+1) oldPresent
    have sameAddress : cursor+32+32*ordinal=cursor+32*(ordinal+1) := by omega
    rw [sameAddress]
    have bounded : cursor+32*(ordinal+1)+32≤2^64 := by
      have bound := suffix.bound
      simp only [MEMORY_BYTES,List.length_cons] at bound
      omega
    rw [cap_high_bytes_read next state _ 32 (by have high := suffix.high; omega)
      bounded frame,slot]
    rfl

/-- Non-consuming low-workspace steps preserve the exact remaining words and
tailBytes tail when their physical cursor and end registers are unchanged. -/
theorem cap_check_word_suffix_frame (state next : MachineState)
    (cursor : Nat) (words : List Digest) (tailBytes : Nat)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (frame : CapHighBytes next state)
    (pointer : next.getReg .x25=state.getReg .x25)
    (endPointer : next.getReg .x22=state.getReg .x22) :
    CapCheckWordSuffix next cursor words tailBytes := by
  refine ⟨pointer.trans suffix.pointer,endPointer.trans suffix.endPointer,
    suffix.high,suffix.bound,suffix.partialBound,?_⟩
  intro ordinal present
  have bounded : cursor+32*ordinal+32≤2^64 := by
    have bound := suffix.bound
    simp only [MEMORY_BYTES] at bound
    omega
  rw [cap_high_bytes_read next state _ 32 (by have high := suffix.high; omega)
    bounded frame]
  exact suffix.slots ordinal present

end CommitGolfCandidate
