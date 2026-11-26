import CommitGolfCandidate.LateNormalPathFacts
import CommitGolfCandidate.LateMemoryStep
import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.HeapLayout
import CommitGolfCandidate.LateBinding

namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

theorem read_buffer_memory_congr (left right : MachineState) (same : left.mem = right.mem)
    (address count : Nat) : readBuffer left address count = readBuffer right address count := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, same]

theorem heap_offset_even (q : Nat) : heapOffset (2*q) = 96*q := by
  unfold heapOffset; omega

theorem heap_offset_odd (q : Nat) : heapOffset (2*q+1) = 96*q+32 := by
  unfold heapOffset; omega

def capParentSetupInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0,
   .ADDI .x10 .x0 0, .SLLI .x10 .x10 11, .ADDI .x10 .x10 4, .SLLI .x10 .x10 11, .ADDI .x10 .x10 448,
   .ADDI .x12 .x0 0, .SLLI .x12 .x12 11, .ADDI .x12 .x12 2, .SLLI .x12 .x12 11, .ADDI .x12 .x12 480]

def capParentSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capParentSetupInstructions.take count).foldl execInstrBr state

def checkCapParentSetupState (state : MachineState) : MachineState :=
  capParentSetupPrefix state 13

theorem check_cap_parent_setup_preserves (state : MachineState) (reg : Reg)
    (kept : reg ∈ [Reg.x8, .x19, .x22, .x24, .x25, .x26, .x27]) :
    (checkCapParentSetupState state).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at kept
  rcases kept with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [checkCapParentSetupState, capParentSetupPrefix, capParentSetupInstructions,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem copy_getMem_setMem (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query =
      if query = address then value else state.getMem query := by
  simp [MachineState.getMem, MachineState.setMem]

theorem copy_getReg_setMem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by
  cases reg <;> rfl

def openingCopyInstructions : List Instr :=
  [.LD .x6 .x23 0, .SD .x25 .x6 0,
   .LD .x6 .x23 8, .SD .x25 .x6 8,
   .LD .x6 .x23 16, .SD .x25 .x6 16,
   .LD .x6 .x23 24, .SD .x25 .x6 24]

def openingCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingCopyInstructions.take count).foldl execInstrBr state

def openingCopyState (state : MachineState) : MachineState :=
  openingCopyPrefix state 8

theorem opening_copy_memory_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 4,
      address ≠ state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) :
    (openingCopyState state).getMem address = state.getMem address := by
  have h0 := outside ⟨0, by decide⟩
  have h1 := outside ⟨1, by decide⟩
  have h2 := outside ⟨2, by decide⟩
  have h3 := outside ⟨3, by decide⟩
  have a0 : address ≠ state.getReg .x25 := by simpa using h0
  have a1 : address ≠ state.getReg .x25 + 8#64 := h1
  have a2 : address ≠ state.getReg .x25 + 16#64 := h2
  have a3 : address ≠ state.getReg .x25 + 24#64 := h3
  simp [openingCopyState, openingCopyPrefix, openingCopyInstructions,
    execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    copy_getReg_setMem, copy_getMem_setMem, signExtend12, a0, a1, a2, a3]

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

theorem opening_copy_expansion (state : MachineState) :
    openingCopyState state =
      ([.LD .x6 .x23 0, .SD .x25 .x6 0,
        .LD .x6 .x23 8, .SD .x25 .x6 8,
        .LD .x6 .x23 16, .SD .x25 .x6 16,
        .LD .x6 .x23 24, .SD .x25 .x6 24] : List Instr).foldl execInstrBr state := rfl

theorem opening_copy_memory (state : MachineState)
    (separated : ∀ source destination : Fin 4,
      state.getReg .x23 + BitVec.ofNat 64 (8 * source.val) ≠
        state.getReg .x25 + BitVec.ofNat 64 (8 * destination.val)) (word : Fin 4) :
    (openingCopyState state).getMem (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) =
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) := by
  have h10 : state.getReg .x23 + 8#64 ≠ state.getReg .x25 := by
    simpa using separated ⟨1, by decide⟩ ⟨0, by decide⟩
  have h20 : state.getReg .x23 + 16#64 ≠ state.getReg .x25 := by
    simpa using separated ⟨2, by decide⟩ ⟨0, by decide⟩
  have h21 : state.getReg .x23 + 16#64 ≠ state.getReg .x25 + 8#64 :=
    separated ⟨2, by decide⟩ ⟨1, by decide⟩
  have h30 : state.getReg .x23 + 24#64 ≠ state.getReg .x25 := by
    simpa using separated ⟨3, by decide⟩ ⟨0, by decide⟩
  have h31 : state.getReg .x23 + 24#64 ≠ state.getReg .x25 + 8#64 :=
    separated ⟨3, by decide⟩ ⟨1, by decide⟩
  have h32 : state.getReg .x23 + 24#64 ≠ state.getReg .x25 + 16#64 :=
    separated ⟨3, by decide⟩ ⟨2, by decide⟩
  fin_cases word <;>
    simp [openingCopyState, openingCopyPrefix, openingCopyInstructions,
      execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      copy_getReg_setMem, signExtend12,
      h10, h20, h21, h30, h31, h32]

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
end CommitGolfCandidate.PairCap
