import CommitGolfCandidate.CapDigestCopy

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capWordCopyInstructions (source destination : Reg) (sourceOffset destinationOffset : Nat) : List Instr :=
  [.LD .x6 source (BitVec.ofNat 12 sourceOffset), .SD destination .x6 (BitVec.ofNat 12 destinationOffset),
   .LD .x6 source (BitVec.ofNat 12 (sourceOffset+8)), .SD destination .x6 (BitVec.ofNat 12 (destinationOffset+8)),
   .LD .x6 source (BitVec.ofNat 12 (sourceOffset+16)), .SD destination .x6 (BitVec.ofNat 12 (destinationOffset+16)),
   .LD .x6 source (BitVec.ofNat 12 (sourceOffset+24)), .SD destination .x6 (BitVec.ofNat 12 (destinationOffset+24))]

def capWordCopyPrefix (source destination : Reg) (sourceOffset destinationOffset : Nat)
    (state : MachineState) (count : Nat) : MachineState :=
  ((capWordCopyInstructions source destination sourceOffset destinationOffset).take count).foldl execInstrBr state

def CapWordCopyFetched (image : Image) (source destination : Reg)
    (sourceOffset destinationOffset : Nat) (entry : Word) : Prop :=
  ∀ state : MachineState, ∀ i < 8, state.pc = entry →
    fetch image (capWordCopyPrefix source destination sourceOffset destinationOffset state i) =
      some (.base (((capWordCopyInstructions source destination sourceOffset destinationOffset)[i]?).getD .EBREAK))

private theorem store_register (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by
  cases reg <;> rfl

theorem cap_word_copy_prefix_succ (source destination : Reg) (sourceOffset destinationOffset : Nat) (state : MachineState) (count : Nat)
    (bounded : count < 8) :
    capWordCopyPrefix source destination sourceOffset destinationOffset state (count + 1) =
      execInstrBr (capWordCopyPrefix source destination sourceOffset destinationOffset state count)
        (((capWordCopyInstructions source destination sourceOffset destinationOffset)[count]?).getD .EBREAK) := by
  interval_cases count <;> rfl

theorem cap_word_copy_prefix_register (source destination : Reg) (sourceOffset destinationOffset : Nat) (state : MachineState) (count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (outside : reg ≠ .x6) :
    (capWordCopyPrefix source destination sourceOffset destinationOffset state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capWordCopyPrefix, capWordCopyInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC, store_register,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_word_copy_prefix_pc (source destination : Reg) (sourceOffset destinationOffset : Nat) (state : MachineState) (count : Nat)
    (bounded : count ≤ 8) :
    (capWordCopyPrefix source destination sourceOffset destinationOffset state count).pc =
      state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capWordCopyPrefix, capWordCopyInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_word_copy_prefix_zero (source destination : Reg)
    (sourceOffset destinationOffset : Nat) (state : MachineState) :
    capWordCopyPrefix source destination sourceOffset destinationOffset state 0 = state := rfl

attribute [local irreducible] capWordCopyPrefix

theorem cap_word_copy_execute (image : Image) (source destination : Reg) (sourceOffset destinationOffset : Nat) (entry : Word)
    (fetched : CapWordCopyFetched image source destination sourceOffset destinationOffset entry)
    (state : MachineState) (pc : state.pc = entry)
    (sourceStable : source ≠ .x6) (destinationStable : destination ≠ .x6)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg source +
        signExtend12 (BitVec.ofNat 12 (sourceOffset + 8 * word.val))) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg destination +
        signExtend12 (BitVec.ofNat 12 (destinationOffset + 8 * word.val))) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (8 + fuel) state allowCoins =
      (do let result ← execute image fuel (capWordCopyPrefix source destination sourceOffset destinationOffset state 8) allowCoins
          return result.charge 8 0) := by
  conv_lhs =>
    arg 3
    rw [← cap_word_copy_prefix_zero source destination sourceOffset destinationOffset state]
  apply execute_unit_steps (states := capWordCopyPrefix source destination sourceOffset destinationOffset state)
  intro i bounded
  refine ⟨.base (((capWordCopyInstructions source destination sourceOffset destinationOffset)[i]?).getD .EBREAK),
    fetched state i bounded pc, ?_, ?_⟩
  · have sourceReg := cap_word_copy_prefix_register source destination sourceOffset destinationOffset state i (by omega)
      source sourceStable
    have destinationReg := cap_word_copy_prefix_register source destination sourceOffset destinationOffset state i (by omega)
      destination destinationStable
    have valid : memoryArgumentsValid (capWordCopyPrefix source destination sourceOffset destinationOffset state i)
        (((capWordCopyInstructions source destination sourceOffset destinationOffset)[i]?).getD .EBREAK) = true := by
      have s0 := sourceValid ⟨0, by decide⟩
      have s1 := sourceValid ⟨1, by decide⟩
      have s2 := sourceValid ⟨2, by decide⟩
      have s3 := sourceValid ⟨3, by decide⟩
      have d0 := destinationValid ⟨0, by decide⟩
      have d1 := destinationValid ⟨1, by decide⟩
      have d2 := destinationValid ⟨2, by decide⟩
      have d3 := destinationValid ⟨3, by decide⟩
      interval_cases i <;>
        simp only [capWordCopyInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid, memAccess,
          sourceReg, destinationReg]
      · simpa only [Nat.mul_zero, Nat.add_zero] using s0
      · simpa only [Nat.mul_zero, Nat.add_zero] using d0
      · exact s1
      · exact d1
      · exact s2
      · exact d2
      · exact s3
      · exact d3
    rw [cap_word_copy_prefix_succ source destination sourceOffset destinationOffset state i bounded]
    interval_cases i <;>
      simp only [capWordCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte]
  · interval_cases i <;> rfl

end CommitGolfCandidate
