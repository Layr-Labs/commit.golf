import CommitGolfCandidate.CursorSaltExecution

/-! Salt loads/stores are unchanged but execute contiguously at the new leaf
entry. Bounds and the actual eight ordinary steps remain explicit. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def ContiguousSaltFetched (image : Image) : Prop :=
  ∀ (state : MachineState) (i : Nat), i < 8 →
    state.pc = BitVec.ofNat 64 (4456 + 4 * i) →
    fetch image state = some (.base ((cursorSaltInstructions[i]?).getD .EBREAK))

/-- Eight ordinary instructions copy the salt into the consumed prefix, with
all accesses checked before taking the corresponding machine step. -/
theorem contiguous_salt_execute (image : Image) (fetched : ContiguousSaltFetched image)
    (state : MachineState) (pc : state.pc = 4456)
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
