import CommitGolfCandidate.CapCheckPathReference
import CommitGolfCandidate.WriteMemory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer writeBits capCheckCompressionState
  checkCompressionState capCheckPathPreparedState checkPathPreparedState
  capCheckPathBlockState checkPathStepState

private theorem compression_memory (state : MachineState) (answer : BitVec 256) :
    (checkCompressionState state answer).mem = (writeBits state 256 answer).mem := by
  unfold checkCompressionState
  exact write_bits_memory_congr _ state 256 answer rfl


private theorem next_memory (state : MachineState) :
    (checkPathNextState state).mem = state.mem := rfl


theorem cap_check_path_block_reference_memory (state : MachineState)
    (answer : BitVec 256) (scratch : state.getReg .x21 = 256) :
    (capCheckPathBlockState state answer).mem = (checkPathStepState state answer).mem := by
  have preparedScratch :=
    (cap_check_path_prepared_register state .x21 (by decide)).trans scratch
  have preparedMemory : (capCheckPathPreparedState state).mem =
      (checkPathPreparedState state).mem := by
    rw [cap_check_path_prepared_reference]
    rfl
  have compression := congrArg MachineState.mem
    (cap_check_compression_reference (capCheckPathPreparedState state) answer preparedScratch)
  have written := write_bits_memory_congr (capCheckPathPreparedState state)
    (checkPathPreparedState state) 256 answer preparedMemory
  unfold capCheckPathBlockState checkPathStepState
  exact (cap_check_path_tail_memory _).trans
    (compression.trans ((compression_memory _ answer).trans
      (written.trans ((compression_memory _ answer).symm.trans (next_memory _).symm))))


theorem cap_check_path_block_digest (state : MachineState) (answer : BitVec 256)
    (scratch : state.getReg .x21 = 256) :
    readBuffer (capCheckPathBlockState state answer) 256 32 = answer := by
  exact (read_buffer_memory_congr (capCheckPathBlockState state answer)
    (checkPathStepState state answer) (cap_check_path_block_reference_memory state answer scratch)
    256 32).trans (check_path_step_digest state answer)


private theorem memory_word_congr (left right : MachineState)
    (same : left.mem = right.mem) (address : Word) :
    left.getMem address = right.getMem address := congrFun same address

theorem cap_check_path_block_outside (state : MachineState) (answer : BitVec 256)
    (scratch : state.getReg .x21 = 256) (address : Word)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (capCheckPathBlockState state answer).getMem address = state.getMem address := by
  exact (memory_word_congr _ _
    (cap_check_path_block_reference_memory state answer scratch) address).trans
      (check_path_step_outside state answer address scratch outside)

end CommitGolfCandidate
