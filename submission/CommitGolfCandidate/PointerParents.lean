import CommitGolfCandidate.ParentPointers
import CommitGolfCandidate.WriteMemory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

abbrev pointerParentQuery (state : MachineState) : PublicSpec.Domain :=
  .inl (readBuffer state (state.getReg .x10).toNat 64)

private theorem parent_read_fixed_width (state : MachineState) (address width : Nat)
    (selected : width = 64) :
    BitVec.setWidth 512 (readBuffer state address width) = readBuffer state address 64 := by
  subst width
  exact BitVec.setWidth_eq _

def pointerParentState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits state (state.getReg .x12) answer

theorem pointer_parent_memory (state : MachineState) (answer : BitVec 256) :
    (pointerParentState state answer).mem =
      (writeBits state (state.getReg .x12) answer).mem := rfl

theorem pointer_parent_register (state : MachineState) (answer : BitVec 256) (reg : Reg) :
    (pointerParentState state answer).getReg reg = state.getReg reg :=
  writeBits_register state _ answer reg

theorem pointer_parent_compression (state : MachineState) (pc : state.pc = 4388)
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 64 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let answer ← World.query (.inr (pointerParentQuery state))
          let result ← execute (submission.image .commit) fuel (pointerParentState state answer) true
          return result.charge 8 1) := by
  have fetched : fetch (submission.image .commit) state = some (.base .ECALL) := by
    apply commit_fetch _ 73 _ (by decide) pc
    rfl
  have input : oracleInput state = some (pointerParentQuery state) := by
    simp [oracleInput, pointerParentQuery, constants.2.2, constants.2.1,
      COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, sourceValid, destinationValid]
    refine ⟨⟨sourceAligned, destinationAligned⟩, ?_⟩
    apply parent_read_fixed_width
    rw [constants.2.2]
    rfl
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos constants.1, input]
  simp [pointerParentState, writeOracleAnswer, constants.2.2,
    oracleCycles, COMPRESSION_CYCLES, Execution.charge]
  rfl

def pointerParentAdvance (state : MachineState) : MachineState :=
  ((state.setReg .x10 (state.getReg .x10 - 64)).setReg .x12 (state.getReg .x12 - 32))

def pointerParentNextState (state : MachineState) : MachineState :=
  (pointerParentAdvance state).setPC
    (if state.getReg .x12 - 32 = state.getReg .x9 then 4404 else 4388)

theorem pointer_parent_exit (state : MachineState) (pc : state.pc = 4404) (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (state.setPC 4412) true
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base (.JAL .x0 8)) := by
    apply commit_fetch _ 77 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JAL .x0 8)) = some (state.setPC 4412) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      pc, MachineState.setReg]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

end CommitGolfCandidate
