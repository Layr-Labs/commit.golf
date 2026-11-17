import CommitGolfCandidate.CursorPositionFrame

/-! The salt-copy execution bridge uses the carried input pointer as the store
destination. Bounds cover each real LD/SD, and neither operation changes x10. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def cursorSaltInstructions : List Instr :=
  [.LD .x6 .x18 0, .SD .x10 .x6 0,
   .LD .x6 .x18 8, .SD .x10 .x6 8,
   .LD .x6 .x18 16, .SD .x10 .x6 16,
   .ADDI .x6 .x6 0, .SD .x10 .x0 24]

def cursorSaltPrefix (state : MachineState) (count : Nat) : MachineState :=
  (cursorSaltInstructions.take count).foldl execInstrBr state

def CursorSaltFetched (image : Image) : Prop :=
  ∀ (state : MachineState) (i : Nat), i < 8 →
    state.pc = BitVec.ofNat 64 (4280 + 4 * i) →
    fetch image state = some (.base ((cursorSaltInstructions[i]?).getD .EBREAK))

theorem cursor_salt_prefix_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (notTemporary : reg ≠ .x6) :
    (cursorSaltPrefix state count).getReg reg = state.getReg reg := by
  have memory (current : MachineState) (address value : Word) (r : Reg) :
      (current.setMem address value).getReg r = current.getReg r := by
    cases r <;> rfl
  interval_cases count <;>
    simp only [cursorSaltPrefix, cursorSaltInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC, memory,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notTemporary)]

/-- Eight ordinary instructions copy the salt into the consumed prefix, with
all accesses checked before taking the corresponding machine step. -/
theorem cursor_salt_execute (image : Image) (fetched : CursorSaltFetched image)
    (state : MachineState) (pc : state.pc = 4280)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x10 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute image (8 + fuel) state true =
      (do let result ← execute image fuel (cursorSaltCopyState state) true
          return result.charge 8 0) := by
  change execute image (8 + fuel) state true =
    (do let result ← execute image fuel (cursorSaltPrefix state 8) true
        return result.charge 8 0)
  apply execute_unit_steps (states := cursorSaltPrefix state)
  intro i hi
  refine ⟨.base ((cursorSaltInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetched _ i hi
    interval_cases i <;>
      simp [cursorSaltPrefix, cursorSaltInstructions, execInstrBr, pc,
        MachineState.setPC]
  · have source := cursor_salt_prefix_register state i (by omega) .x18 (by decide)
    have destination := cursor_salt_prefix_register state i (by omega) .x10 (by decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (cursorSaltPrefix state i)
        ((cursorSaltInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [cursorSaltInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid,
          memAccess, source, destination, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [cursorSaltInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate
