import CommitGolfCandidate.CursorParentFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] readBuffer

theorem fused_parent_query_pc (state : MachineState) (pc : Word) :
    commitParentQuery (state.setPC pc) = commitParentQuery state := by
  unfold commitParentQuery pointerParentQuery
  rw [read_buffer_memory_congr (state.setPC pc) state rfl]
  rfl

theorem fused_parent_reply_pc (state : MachineState) (pc : Word) (answer : BitVec 256) :
    commitParentState (state.setPC pc) answer =
      (commitParentState state answer).setPC (pc + 4) := by
  unfold commitParentState pointerParentState
  change writeBits (state.setPC pc) (state.getReg .x12) answer =
    (writeBits state (state.getReg .x12) answer).setPC (pc + 4)
  exact hoist_write_bits_pc _ _ _ _

theorem fused_parent_next_pc (state : MachineState) (pc : Word) :
    commitParentNextState (state.setPC pc) = commitParentNextState state := by
  cases state
  rfl

theorem fused_parent_compression (image : Image) (state : MachineState)
    (fetched : fetch image state = some (.base .ECALL))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 64 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (fuel : Nat) :
    execute image (1 + fuel) state true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute image fuel (commitParentState state answer) true
          return result.charge 8 1) := by
  have input : oracleInput state = some (commitParentQuery state) := by
    simp [oracleInput, commitParentQuery, pointerParentQuery, constants.2.2, constants.2.1,
      COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, sourceValid, destinationValid]
    refine ⟨⟨sourceAligned, destinationAligned⟩, ?_⟩
    rw [constants.2.2]
    exact BitVec.setWidth_eq _
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos constants.1, input]
  simp [commitParentState, pointerParentState, writeOracleAnswer, constants.2.2,
    oracleCycles, COMPRESSION_CYCLES, Execution.charge]
  rfl

end CommitGolfCandidate
