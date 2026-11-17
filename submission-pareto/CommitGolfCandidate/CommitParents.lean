import CommitGolfCandidate.Commit
import CommitGolfCandidate.WriteMemory

/-! Bottom-up parent construction and successful commitment return. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

abbrev commitParentQuery (state : MachineState) : PublicSpec.Domain :=
  .inl (readBuffer state (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat 64)

private def parentInstructions : List Instr :=
  [.SLLI .x6 .x20 6, .ADD .x10 .x9 .x6, .SLLI .x7 .x20 5, .ADD .x12 .x9 .x7,
   .JAL .x0 12]

private def parentPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentInstructions.take count).foldl execInstrBr state

def commitParentState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits (parentPrefix state 5) (state.getReg .x9 + (state.getReg .x20 <<< 5)) answer

/-- Leaf hashing establishes these constants; parent hashing preserves them. -/
def ParentOracleRegisters (state : MachineState) : Prop :=
  state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0

theorem commit_parent_oracle_registers (state : MachineState) (answer : BitVec 256)
    (arguments : ParentOracleRegisters state) :
    ParentOracleRegisters (commitParentState state answer) := by
  unfold ParentOracleRegisters at arguments ⊢
  simp only [commitParentState, writeBits_register]
  simpa [parentPrefix,
    parentInstructions, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.setPC] using arguments

/-- The parent's setup instructions do not change memory; its only write is the
compression reply at the parent heap slot. -/
theorem commit_parent_written_memory (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).mem =
      (writeBits state (state.getReg .x9+(state.getReg .x20 <<< 5)) answer).mem :=
  write_bits_memory_congr _ state _ answer rfl

/-- Read two consecutive child digests and write their compression at the parent
index. Four address instructions, one jump and the syscall cost thirteen cycles. -/
theorem commit_parent_compression (state : MachineState) (pc : state.pc = 4348)
    (arguments : ParentOracleRegisters state)
    (sourceValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 6)) 64 = true)
    (destinationValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 5)) 32 = true)
    (sourceAligned : (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x9 + (state.getReg .x20 <<< 5)).toNat % 8 = 0)
    (fuel : Nat) :
    execute (submission.image .commit) (6 + fuel) state true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute (submission.image .commit) fuel (commitParentState state answer) true
          return result.charge 13 1) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (5 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (parentPrefix state 5) true
            return result.charge 5 0) := by
    apply execute_unit_steps (states := parentPrefix state)
    intro i hi
    refine ⟨.base ((parentInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (63 + i) _ (by omega)
      · interval_cases i <;> simp [parentPrefix, parentInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let ready := parentPrefix state 5
  have fetched : fetch (submission.image .commit) ready = some (.base .ECALL) := by
    apply commit_fetch _ 70 _ (by decide)
    · simp [ready, parentPrefix, parentInstructions, execInstrBr, signExtend21,
        pc, MachineState.setReg, MachineState.setPC]
    · rfl
  have registers : ready.getReg .x5 = 0 ∧
      ready.getReg .x10 = state.getReg .x9 + (state.getReg .x20 <<< 6) ∧
      ready.getReg .x11 = 64 ∧
      ready.getReg .x12 = state.getReg .x9 + (state.getReg .x20 <<< 5) ∧
      ready.getReg .x13 = 0 := by
    rcases arguments with ⟨mode, width, primitive⟩
    simp_all [ready, parentPrefix, parentInstructions, execInstrBr,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have memory (address : Nat) : readBuffer ready address 64 = readBuffer state address 64 := rfl
  have input : oracleInput ready = some (commitParentQuery state) := by
    unfold oracleInput
    rw [registers.2.2.2.2, registers.2.1, registers.2.2.1, registers.2.2.2.1]
    simp [commitParentQuery, COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH,
      sourceValid, destinationValid, memory]
    exact ⟨by simpa using sourceAligned, by simpa using destinationAligned⟩
  rw [show 6 + fuel = 5 + (fuel + 1) by omega, setup, execute, fetched,
    if_pos registers.1, input]
  simp [commitParentQuery, writeOracleAnswer, registers.2.2.2.1, commitParentState, ready,
    oracleCycles, COMPRESSION_CYCLES, Execution.charge, ← Nat.add_assoc]
  rfl

theorem commit_parent_pc (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).pc = state.pc + 32 := by
  simp [commitParentState, writeBits, parentPrefix, parentInstructions, execInstrBr,
    signExtend21, MachineState.setReg, MachineState.setPC, BitVec.add_assoc]

theorem commit_parent_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∈ [Reg.x9, .x19, .x20, .x21, .x26]) :
    (commitParentState state answer).getReg reg = state.getReg reg := by
  rw [commitParentState, writeBits_register]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at preserved
  rcases preserved with rfl | rfl | rfl | rfl | rfl <;>
    simp [parentPrefix, parentInstructions,
      execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC]

def commitParentNextState (state : MachineState) : MachineState :=
  (state.setReg .x20 (state.getReg .x20 - 1)).setPC
    (if state.getReg .x20 - 1 = 0 then 4388 else 4348)

theorem commit_parent_next (state : MachineState) (pc : state.pc = 4380) (fuel : Nat) :
    execute (submission.image .commit) (2 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitParentNextState state) true
          return result.charge 2 0) := by
  let next := (state.setReg .x20 (state.getReg .x20 - 1)).setPC 4384
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x20 .x20 4095)) := by
    apply commit_fetch _ 71 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.BNE .x20 .x0 8156)) := by
    apply commit_fetch _ 72 _ (by decide) rfl; rfl
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

/-- One parent costs fifteen cycles and one public query. -/
theorem commit_parent (state : MachineState) (pc : state.pc = 4348)
    (arguments : ParentOracleRegisters state)
    (sourceValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 6)) 64 = true)
    (destinationValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 5)) 32 = true)
    (sourceAligned : (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x9 + (state.getReg .x20 <<< 5)).toNat % 8 = 0)
    (fuel : Nat) :
    execute (submission.image .commit) (8 + fuel) state true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute (submission.image .commit) fuel
            (commitParentNextState (commitParentState state answer)) true
          return result.charge 15 1) := by
  rw [show 8 + fuel = 6 + (2 + fuel) by omega,
    commit_parent_compression state pc arguments sourceValid destinationValid sourceAligned destinationAligned]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (commitParentQuery state))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have nextPC : (commitParentState state answer).pc = 4380 := by rw [commit_parent_pc, pc]; rfl
  rw [commit_parent_next _ nextPC]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
