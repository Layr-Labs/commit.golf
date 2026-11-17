import CommitGolfCandidate.CapCheckLeafReferenceMemory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer capCheckLeafCopyState checkLeafCopyState
  capCheckLeafBlockState checkLeafStepState

theorem cap_check_leaf_query_reference (state : MachineState)
    (scratch : state.getReg .x21 = 256)
    (aligned : (state.getReg .x8).toNat % 8 = 0)
    (separated : ∀ i < 4, ∀ j < 4,
      state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j)) :
    readBuffer (capCheckLeafCopyState state) 256 64 =
      readBuffer state (state.getReg .x8).toNat 32 ++ readBuffer state 256 32 := by
  rw [cap_check_leaf_copy_reference]
  exact check_leaf_input state scratch aligned separated

theorem cap_check_leaf_block_digest (state : MachineState) (answer : BitVec 256)
    (scratch : state.getReg .x21 = 256) :
    readBuffer (capCheckLeafBlockState state answer) 256 32 = answer :=
  (read_buffer_memory_congr _ _
    (cap_check_leaf_block_reference_memory state answer scratch) 256 32).trans
      (check_leaf_step_digest state answer)

private theorem memory_word_congr (left right : MachineState)
    (same : left.mem = right.mem) (address : Word) :
    left.getMem address = right.getMem address :=
  congrFun same address

theorem cap_check_leaf_block_outside (state : MachineState) (answer : BitVec 256)
    (scratch : state.getReg .x21 = 256) (address : Word)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256 + 8*i)) :
    (capCheckLeafBlockState state answer).getMem address = state.getMem address := by
  exact (memory_word_congr _ _
    (cap_check_leaf_block_reference_memory state answer scratch) address).trans
      (check_leaf_step_outside state answer address scratch outside)

end CommitGolfCandidate
