import CommitGolfCandidate.CapCheckPathReference
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.S6CheckTrunc

/-! Lower-path data refinement uses only compiled preparation and write-memory
identities. Up to the reply, published path digest/locality lemmas apply to the
identical ordered data effects; the latch writes no memory, so the scratch digest
is the whole reply (`s6Trunc` keeps every bit). -/
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


theorem cap_check_path_reply_reference_memory (state : MachineState)
    (answer : BitVec 256) (scratch : state.getReg .x21 = 256) :
    (capCheckCompressionState (capCheckPathPreparedState state) answer).mem =
      (checkPathStepState state answer).mem := by
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
  unfold checkPathStepState
  exact compression.trans ((compression_memory _ answer).trans
      (written.trans ((compression_memory _ answer).symm.trans (next_memory _).symm)))

theorem cap_check_path_block_memory (state : MachineState) (answer : BitVec 256)
    (scratch : state.getReg .x21 = 256) :
    (capCheckPathBlockState state answer).mem =
      (capCheckCompressionState (capCheckPathPreparedState state) answer).mem := by
  unfold capCheckPathBlockState
  rw [cap_check_path_tail_memory]

theorem cap_check_path_block_digest (state : MachineState) (answer : BitVec 256)
    (scratch : state.getReg .x21 = 256) :
    readBuffer (capCheckPathBlockState state answer) 256 32 = s6Trunc answer := by
  show _ = answer
  rw [read_buffer_memory_congr _ _ (cap_check_path_block_memory state answer scratch),
    read_buffer_memory_congr _ (checkPathStepState state answer)
      (cap_check_path_reply_reference_memory state answer scratch),
    check_path_step_digest state answer]

private theorem memory_word_congr (left right : MachineState)
    (same : left.mem = right.mem) (address : Word) :
    left.getMem address = right.getMem address := congrFun same address

theorem cap_check_path_block_outside (state : MachineState) (answer : BitVec 256)
    (scratch : state.getReg .x21 = 256) (address : Word)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (capCheckPathBlockState state answer).getMem address = state.getMem address := by
  rw [memory_word_congr _ _ (cap_check_path_block_memory state answer scratch) address]
  exact (memory_word_congr _ _
    (cap_check_path_reply_reference_memory state answer scratch) address).trans
      (check_path_step_outside state answer address scratch outside)

end CommitGolfCandidate
