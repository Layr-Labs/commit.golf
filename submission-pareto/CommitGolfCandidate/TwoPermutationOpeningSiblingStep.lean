import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setMem getReg_setReg

set_option maxRecDepth 4096

def siblingSource (state : MachineState) : Word :=
  state.getReg .x9 + ((state.getReg .x6 ^^^ 1#64) <<< 5)

def siblingDestWord (state : MachineState) (level : Nat) : Word :=
  state.getReg .x21 + BitVec.ofNat 64 (16 + 32*level)

theorem store_offset_eq : ∀ (level : Fin 16) (word : Fin 4),
    signExtend12 (storeOffset level.val word.val) =
      BitVec.ofNat 64 (16 + 32*level.val) + BitVec.ofNat 64 (8*word.val) := by decide

def siblingPrefix (state : MachineState) (level count : Nat) : MachineState :=
  ((siblingInstructions level).take count).foldl execInstrBr state

private theorem siblingPrefix_succ (state : MachineState) (level i : Nat) (bounded : i < 12) :
    siblingPrefix state level (i + 1) =
      execInstrBr (siblingPrefix state level i) ((siblingInstructions level)[i]?.getD .EBREAK) := by
  have existsIndex : i < (siblingInstructions level).length := bounded
  rw [siblingPrefix, siblingPrefix, List.take_succ_eq_append_getElem existsIndex,
    List.foldl_append, List.getElem?_eq_getElem existsIndex]
  rfl

private theorem sibling_ordinary (state : MachineState) (level : Nat) (i : Fin 12)
    (valid : memoryArgumentsValid state ((siblingInstructions level)[i.val]?.getD .EBREAK) = true) :
    ordinaryStep state (.base ((siblingInstructions level)[i.val]?.getD .EBREAK)) =
      some (execInstrBr state ((siblingInstructions level)[i.val]?.getD .EBREAK)) := by
  fin_cases i <;>
    simp [siblingInstructions] at valid ⊢ <;>
    exact ite_eq_left valid

theorem sibling_pc (state : MachineState) (level i : Nat) (bound : i ≤ 12) :
    (siblingPrefix state level i).pc = state.pc + BitVec.ofNat 64 (4*i) := by
  interval_cases i <;> simp [siblingPrefix, siblingInstructions, execInstrBr, MachineState.setPC, BitVec.add_assoc]

/-- Run one of the sixteen straight-line copies at its instruction address. -/
theorem execute_sibling (state : MachineState) (level : Fin 16)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4*(38 + 12*level.val))) (fuel : Nat)
    (allowCoins : Bool) (source : ∀ i : Fin 4,
      accessValid (siblingSource state + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (destination : ∀ i : Fin 4,
      accessValid (siblingDestWord state level.val + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    execute openingImage (12 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (siblingPrefix state level 12) allowCoins
          return result.charge 12 0) := by
  apply execute_unit_steps (states := siblingPrefix state level)
  intro i bounded
  refine ⟨.base ((siblingInstructions level)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (38 + 12 * level.val + i) _ (by have h := level.isLt; omega)
      _ (sibling_decode level ⟨i, bounded⟩)
    rw [sibling_pc _ _ _ (by omega), pc, ← BitVec.ofNat_add]
    congr 1
    omega
  · rw [siblingPrefix_succ state level i bounded]
    apply sibling_ordinary _ level ⟨i, bounded⟩
    have src0 : accessValid (siblingSource state) 8 = true := by simpa using source 0
    have src1 : accessValid (siblingSource state + 8#64) 8 = true := source 1
    have src2 : accessValid (siblingSource state + 16#64) 8 = true := source 2
    have src3 : accessValid (siblingSource state + 24#64) 8 = true := source 3
    have dst0 : accessValid (siblingDestWord state level) 8 = true := by simpa using destination 0
    have dst1 : accessValid (siblingDestWord state level + 8#64) 8 = true := destination 1
    have dst2 : accessValid (siblingDestWord state level + 16#64) 8 = true := destination 2
    have dst3 : accessValid (siblingDestWord state level + 24#64) 8 = true := destination 3
    simp only [siblingSource] at src0 src1 src2 src3
    have o0 := store_offset_eq level 0
    have o1 := store_offset_eq level 1
    have o2 := store_offset_eq level 2
    have o3 := store_offset_eq level 3
    simp only [Fin.val_zero, Fin.val_one] at o0 o1
    change signExtend12 (storeOffset level 2) = BitVec.ofNat 64 (16+32*level.val) + 16#64 at o2
    change signExtend12 (storeOffset level 3) = BitVec.ofNat 64 (16+32*level.val) + 24#64 at o3
    simp only [signExtend12] at o0 o1 o2 o3
    simp only [siblingDestWord] at dst0 dst1 dst2 dst3
    interval_cases i <;>
      simp [memoryArgumentsValid, memAccess, siblingPrefix, siblingInstructions, execInstrBr,
        o0, o1, o2, o3, ← BitVec.add_assoc, signExtend12, src0, src1, src2, src3, dst0, dst1, dst2, dst3]
  · interval_cases i <;> rfl

end TwoPermutationPrototype.Opening
