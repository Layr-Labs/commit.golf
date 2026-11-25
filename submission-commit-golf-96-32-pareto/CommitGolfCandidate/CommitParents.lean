import CommitGolfCandidate.Commit
import CommitGolfCandidate.WriteMemory

/-! Bottom-up parent construction and successful commitment return. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

abbrev commitParentQuery (state : MachineState) : PublicSpec.Domain :=
  .inl (padInput (readBuffer state (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat 64))

private def parentInstructions : List Instr :=
  [.SLLI .x6 .x20 6, .ADD .x10 .x9 .x6, .SLLI .x7 .x20 5, .ADD .x12 .x9 .x7,
   .ADDI .x5 .x0 0, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0]

private def parentPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentInstructions.take count).foldl execInstrBr state

def commitParentState (state : MachineState) (answer : BitVec 256) : MachineState :=
  paddedCompressionState (parentPrefix state 7) answer

/-- The parent's setup instructions do not change memory; its only write is the
compression reply at the parent heap slot. -/
theorem commit_parent_written_memory (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).mem =
      (writeBits state (state.getReg .x9+(state.getReg .x20 <<< 5)) answer).mem :=
  by
    rw [commitParentState, padded_compression_memory]
    exact write_bits_memory_congr _ state _ answer rfl

/-- Read two consecutive child digests and write their compression at the parent
index. Seven setup instructions plus the padded call cost 31 cycles. -/
theorem commit_parent_compression (state : MachineState) (pc : state.pc = 4376)
    (sourceValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 6)) 96 = true)
    (destinationValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 5)) 32 = true)
    (sourceAligned : (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x9 + (state.getReg .x20 <<< 5)).toNat % 8 = 0)
    (beforePadding : (state.getReg .x9 + (state.getReg .x20 <<< 5)).toNat+32 ≤
      (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat+64)
    (fuel : Nat) :
    execute (submission.image .commit) (24 + fuel) state true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute (submission.image .commit) fuel (commitParentState state answer) true
          return result.charge 31 1) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (7 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (parentPrefix state 7) true
            return result.charge 7 0) := by
    apply execute_unit_steps (states := parentPrefix state)
    intro i hi
    refine ⟨.base ((parentInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (70 + i) _ (by omega)
      · interval_cases i <;> simp [parentPrefix, parentInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let ready := parentPrefix state 7
  have readyPC : ready.pc = 4404 := by
    simp [ready, parentPrefix, parentInstructions, execInstrBr, pc, MachineState.setPC]
  have registers : ready.getReg .x5 = 0 ∧
      ready.getReg .x10 = state.getReg .x9 + (state.getReg .x20 <<< 6) ∧
      ready.getReg .x11 = 64 ∧
      ready.getReg .x12 = state.getReg .x9 + (state.getReg .x20 <<< 5) ∧
      ready.getReg .x13 = 0 := by
    simp [ready, parentPrefix, parentInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have call := padding_call false ready 77 (by simp [paddingCallSite]) readyPC
    registers.1 registers.2.2.2.2
    (by rw [registers.2.1]; exact sourceValid)
    (by rw [registers.2.2.2.1]; exact destinationValid)
    (by rw [registers.2.1]; exact sourceAligned)
    (by rw [registers.2.2.2.1]; exact destinationAligned)
    (by rw [registers.2.1, registers.2.2.2.1]; exact beforePadding) fuel true
  simp only [paddingProgram, ↓reduceIte] at call
  rw [show 24+fuel = 7+(17+fuel) by omega, setup]
  erw [call]
  simp only [bind_assoc, pure_bind]
  rw [registers.2.1]
  change ((liftM (World.query (.inr (commitParentQuery state)))) >>= _) = _
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (commitParentQuery state))) : OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  simp [commitParentState, ready, Execution.charge, ← Nat.add_assoc]

theorem commit_parent_pc (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).pc = state.pc + 32 := by
  simp [commitParentState, padded_compression_pc, parentPrefix, parentInstructions, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

theorem commit_parent_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∈ [Reg.x9, .x19, .x20, .x21, .x26]) :
    (commitParentState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at preserved
  rcases preserved with rfl | rfl | rfl | rfl | rfl <;>
    rw [commitParentState, padded_compression_register _ _ _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] <;>
    simp [parentPrefix, parentInstructions,
      execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC]

def commitParentNextState (state : MachineState) : MachineState :=
  (state.setReg .x20 (state.getReg .x20 - 1)).setPC
    (if state.getReg .x20 - 1 = 0 then 4416 else 4376)

theorem commit_parent_next (state : MachineState) (pc : state.pc = 4408) (fuel : Nat) :
    execute (submission.image .commit) (2 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitParentNextState state) true
          return result.charge 2 0) := by
  let next := (state.setReg .x20 (state.getReg .x20 - 1)).setPC 4412
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x20 .x20 4095)) := by
    apply commit_fetch _ 78 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.BNE .x20 .x0 8156)) := by
    apply commit_fetch _ 79 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x20 .x20 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc, BitVec.sub_eq_add_neg]
  have s1 : ordinaryStep next (.base (.BNE .x20 .x0 8156)) = some (commitParentNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, commitParentNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [show 2 + fuel = (fuel + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ f0 s0, execute_ordinary_step _ _ _ _ _ _ f1 s1]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- One parent costs 33 cycles and one public query. -/
theorem commit_parent (state : MachineState) (pc : state.pc = 4376)
    (sourceValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 6)) 96 = true)
    (destinationValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 5)) 32 = true)
    (sourceAligned : (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x9 + (state.getReg .x20 <<< 5)).toNat % 8 = 0)
    (beforePadding : (state.getReg .x9 + (state.getReg .x20 <<< 5)).toNat+32 ≤
      (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat+64)
    (fuel : Nat) :
    execute (submission.image .commit) (26 + fuel) state true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute (submission.image .commit) fuel
            (commitParentNextState (commitParentState state answer)) true
          return result.charge 33 1) := by
  rw [show 26 + fuel = 24 + (2 + fuel) by omega,
    commit_parent_compression state pc sourceValid destinationValid sourceAligned destinationAligned beforePadding]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (commitParentQuery state))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have nextPC : (commitParentState state answer).pc = 4408 := by rw [commit_parent_pc, pc]; rfl
  rw [commit_parent_next _ nextPC]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
