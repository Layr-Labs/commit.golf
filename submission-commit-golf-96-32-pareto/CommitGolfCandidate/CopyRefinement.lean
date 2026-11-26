import CommitGolfCandidate.Memory
import CommitGolfCandidate.Opening

/-! Digest-copy (32 B) and salt-copy (16 B) contents and preservation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Registers and the program counter do not affect buffer reads. -/
theorem read_buffer_memory_congr (left right : MachineState) (same : left.mem = right.mem)
    (address count : Nat) : readBuffer left address count = readBuffer right address count := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, same]

/-- Disjoint, non-wrapping digest buffers have distinct word addresses. -/
theorem separate_digest_words (left right i j : Nat)
    (leftBound : left+32 ≤ 2^64) (rightBound : right+32 ≤ 2^64)
    (iBound : i < 4) (jBound : j < 4)
    (separate : left+32 ≤ right ∨ right+32 ≤ left) :
    BitVec.ofNat 64 (left+8*i) ≠ BitVec.ofNat 64 (right+8*j) := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : left+8*i < 2^64),
    Nat.mod_eq_of_lt (by omega : right+8*j < 2^64)] at natural
  rcases separate with before | after <;> omega

/-- Disjoint, non-wrapping 16-byte buffers have distinct word addresses. -/
theorem separate_salt_words (left right i j : Nat)
    (leftBound : left+16 ≤ 2^64) (rightBound : right+16 ≤ 2^64)
    (iBound : i < 2) (jBound : j < 2)
    (separate : left+16 ≤ right ∨ right+16 ≤ left) :
    BitVec.ofNat 64 (left+8*i) ≠ BitVec.ofNat 64 (right+8*j) := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : left+8*i < 2^64),
    Nat.mod_eq_of_lt (by omega : right+8*j < 2^64)] at natural
  rcases separate with before | after <;> omega

/-- The actual four-word copy reproduces its complete source digest. -/
theorem opening_copy_digest (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x23 = BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source+32 ≤ 2^64) (destinationBound : destination+32 ≤ 2^64)
    (separate : source+32 ≤ destination ∨ destination+32 ≤ source) :
    readBuffer (openingCopyState state) destination 32 = readBuffer state source 32 := by
  apply (read_digest_eq_iff _ _ _ _ destinationAligned sourceAligned).mpr
  intro word inside
  have copied := opening_copy_memory state (by
    intro i j
    rw [sourcePointer, destinationPointer, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact separate_digest_words source destination i.val j.val sourceBound destinationBound
      i.isLt j.isLt separate) ⟨word, inside⟩
  simpa only [sourcePointer, destinationPointer, ← BitVec.ofNat_add] using copied

/-- A disjoint digest is unaffected by the four-word copy. -/
theorem opening_copy_preserves_digest (state : MachineState) (destination address : Nat)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (openingCopyState state) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi
  apply opening_copy_memory_outside
  intro j
  rw [destinationPointer, ← BitVec.ofNat_add]
  exact separate_digest_words address destination i j.val readBound destinationBound hi j.isLt separate

/-- The actual two-word salt copy reproduces its complete 16-byte source salt. -/
theorem opening_salt_copy_salt (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x23 = BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source+16 ≤ 2^64) (destinationBound : destination+16 ≤ 2^64)
    (separate : source+16 ≤ destination ∨ destination+16 ≤ source) :
    readBuffer (openingSaltCopyState state) destination 16 = readBuffer state source 16 := by
  apply (read_salt_eq_iff _ _ _ _ destinationAligned sourceAligned).mpr
  intro word inside
  have copied := opening_salt_copy_memory state (by
    intro i j
    rw [sourcePointer, destinationPointer, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact separate_salt_words source destination i.val j.val sourceBound destinationBound
      i.isLt j.isLt separate) ⟨word, inside⟩
  simpa only [sourcePointer, destinationPointer, ← BitVec.ofNat_add] using copied

/-- A disjoint digest is unaffected by the two-word salt copy. -/
theorem opening_salt_copy_preserves_digest (state : MachineState) (destination address : Nat)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+16 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+16 ≤ address) :
    readBuffer (openingSaltCopyState state) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi
  apply opening_salt_copy_memory_outside
  intro j
  rw [destinationPointer, ← BitVec.ofNat_add]
  intro equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address+8*i < 2^64),
    Nat.mod_eq_of_lt (by have := j.isLt; omega : destination+8*j.val < 2^64)] at natural
  have := j.isLt
  rcases separate with before | after <;> omega

end CommitGolfCandidate
