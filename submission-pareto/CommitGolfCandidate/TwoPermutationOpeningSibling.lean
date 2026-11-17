import CommitGolfCandidate.TwoPermutationOpeningSiblingStep
import CommitGolfCandidate.TwoPermutationOpeningCopy

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setMem getReg_setReg

set_option maxRecDepth 4096

@[local simp] private theorem mem_setReg (s : MachineState) (r : Reg) (w : Word) :
    (s.setReg r w).mem = s.mem := by cases r <;> rfl

@[local simp] private theorem mem_setPC (s : MachineState) (w : Word) :
    (s.setPC w).mem = s.mem := rfl

@[local simp] private theorem sibling_zero (s : MachineState) : s.getReg .x0 = 0#64 := rfl

private theorem stored_memory (state : MachineState) (address value : Word) :
    (state.setMem address value).mem =
      fun x => if x = address then value else state.mem x := by
  funext x
  simp [MachineState.setMem]

/-- Each word goes to its fixed offset from the record pointer. -/
theorem sibling_memory (state : MachineState) (level : Nat) (inside : level < 16)
    (separate : ∀ i j : Fin 4, siblingSource state + BitVec.ofNat 64 (8 * i.val) ≠
      siblingDestWord state level + BitVec.ofNat 64 (8 * j.val)) :
    (siblingPrefix state level 12).mem =
      (fourWordStore state (siblingSource state) (siblingDestWord state level)).mem := by
  have h10 := separate 1 0
  have h20 := separate 2 0
  have h21 := separate 2 1
  have h30 := separate 3 0
  have h31 := separate 3 1
  have h32 := separate 3 2
  have os (j : Fin 4) := store_offset_eq (⟨level, inside⟩ : Fin 16) j
  have o0 : signExtend12 (storeOffset level 0) = BitVec.ofNat 64 (16+32*level) + 0#64 := os 0
  have o1 : signExtend12 (storeOffset level 1) = BitVec.ofNat 64 (16+32*level) + 8#64 := os 1
  have o2 : signExtend12 (storeOffset level 2) = BitVec.ofNat 64 (16+32*level) + 16#64 := os 2
  have o3 : signExtend12 (storeOffset level 3) = BitVec.ofNat 64 (16+32*level) + 24#64 := os 3
  simp only [signExtend12] at o0 o1 o2 o3
  simp [siblingSource, siblingDestWord] at h10 h20 h21 h30 h31 h32
  simp [siblingPrefix, siblingInstructions, siblingSource, siblingDestWord, fourWordStore,
    execInstrBr, o0, o1, o2, o3, ← BitVec.add_assoc, signExtend12, h10, h20, h21, h30, h31, h32,
    mem_setReg, mem_setPC, stored_memory]

/-- Registers outside the path, destination, counter and temporaries are preserved. -/
theorem sibling_register (state : MachineState) (level : Nat) (register : Reg)
    (node : register ≠ .x6) (source : register ≠ .x7) (dest : register ≠ .x21)
    (count : register ≠ .x29) (temp : register ≠ .x31) :
    (siblingPrefix state level 12).getReg register = state.getReg register := by
  simp [siblingPrefix, siblingInstructions, execInstrBr, signExtend12,
      Ne.symm node, Ne.symm source, Ne.symm dest, Ne.symm count, Ne.symm temp]

end TwoPermutationPrototype.Opening
