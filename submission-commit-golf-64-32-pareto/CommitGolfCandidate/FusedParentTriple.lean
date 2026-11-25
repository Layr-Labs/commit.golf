import CommitGolfCandidate.FusedParentFrame

/-! A parent query followed by two pointer decrements executes without a branch.
Its PC-normalized state matches one retained reference parent, for every answer. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState readBuffer

def ParentTripleFetched (image : Image) (start : Word) : Prop :=
  ∀ state : MachineState,
    (state.pc = start → fetch image state = some (.base .ECALL)) ∧
    (state.pc = start + 4 →
      fetch image state = some (.base (.ADDI .x10 .x10 4032))) ∧
    (state.pc = start + 8 →
      fetch image state = some (.base (.ADDI .x12 .x12 4064)))

def parentAdvancePrefix (state : MachineState) (count : Nat) : MachineState :=
  ([Instr.ADDI .x10 .x10 4032, .ADDI .x12 .x12 4064].take count).foldl execInstrBr state

theorem fused_parent_advance_pc (state : MachineState) (pc : Word) :
    pointerParentAdvance (state.setPC pc) = (pointerParentAdvance state).setPC pc := by
  cases state
  rfl

theorem fused_parent_advance_state (state : MachineState) :
    parentAdvancePrefix state 2 =
      (pointerParentAdvance state).setPC (state.pc + 8) := by
  simp [parentAdvancePrefix, List.foldl, execInstrBr, pointerParentAdvance,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem fused_parent_advance_execute (image : Image) (start : Word)
    (fetched : ParentTripleFetched image start) (state : MachineState)
    (pc : state.pc = start + 4) (fuel : Nat) :
    execute image (2 + fuel) state true =
      (do let result ← execute image fuel
            ((pointerParentAdvance state).setPC (state.pc + 8)) true
          return result.charge 2 0) := by
  have trace : execute image (2 + fuel) state true =
      (do let result ← execute image fuel (parentAdvancePrefix state 2) true
          return result.charge 2 0) := by
    apply execute_unit_steps (states := parentAdvancePrefix state)
    intro i hi
    refine ⟨.base (([Instr.ADDI .x10 .x10 4032, .ADDI .x12 .x12 4064][i]?).getD .EBREAK),
      ?_, ?_, ?_⟩
    · interval_cases i
      · apply (fetched state).2.1 pc
      · apply (fetched (parentAdvancePrefix state 1)).2.2
        change state.pc + 4 = start + 8
        rw [pc, BitVec.add_assoc]
        rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  rw [fused_parent_advance_state] at trace
  exact trace

theorem fused_parent_step_frame (state : MachineState) (pc : Word) (answer : BitVec 256) :
    (pointerParentAdvance (commitParentState (state.setPC pc) answer)).setPC (pc + 12) =
      (commitParentNextState (commitParentState state answer)).setPC (pc + 12) := by
  rw [fused_parent_reply_pc, fused_parent_advance_pc, hoist_pc_pc]
  unfold commitParentNextState pointerParentNextState
  rw [hoist_pc_pc]

/-- Exactly three instructions, ten cycles and one public query. -/
theorem fused_parent_triple (image : Image) (start : Word)
    (fetched : ParentTripleFetched image start) (state : MachineState)
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 64 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (fuel : Nat) :
    execute image (3 + fuel) (state.setPC start) true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute image fuel
            ((commitParentNextState (commitParentState state answer)).setPC (start + 12)) true
          return result.charge 10 1) := by
  rw [show 3 + fuel = 1 + (2 + fuel) by omega,
    fused_parent_compression image (state.setPC start) ((fetched _).1 rfl)
      constants sourceValid destinationValid sourceAligned destinationAligned]
  have input : readBuffer (state.setPC start) (state.getReg .x10).toNat 64 =
      readBuffer state (state.getReg .x10).toNat 64 :=
    read_buffer_memory_congr (state.setPC start) state rfl _ _
  simp only [commitParentQuery, pointerParentQuery]
  change (do let answer ← (liftM (World.query (.inr (.inl
              (readBuffer (state.setPC start) (state.getReg .x10).toNat 64)))) :
              OracleComp World (BitVec 256))
             let result ← execute image (2 + fuel) (commitParentState (state.setPC start) answer) true
             return result.charge 8 1) = _
  rw [input]
  apply congrArg (fun tail =>
    (liftM (World.query (.inr (commitParentQuery state))) :
      OracleComp World (BitVec 256)) >>= tail)
  funext answer
  change BitVec 256 at answer
  have nextPC : (commitParentState (state.setPC start) answer).pc = start + 4 := by
    rw [commit_parent_pc]
    rfl
  rw [fused_parent_advance_execute image start fetched _ nextPC]
  rw [nextPC, BitVec.add_assoc]
  simp only [bind_assoc, pure_bind]
  change (do let result ← execute image fuel
              ((pointerParentAdvance (commitParentState (state.setPC start) answer)).setPC
                (start + 12)) true
             return (result.charge 2 0).charge 8 1) = _
  rw [fused_parent_step_frame]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
