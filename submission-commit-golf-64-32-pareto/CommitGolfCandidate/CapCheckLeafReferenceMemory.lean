import CommitGolfCandidate.CapCheckLeafReferenceBase

/-! Memory and query projections of the relocated checker block. The compiled
copy/compression identities form an opaque interface to the published semantics;
only the latch's memory projection is needed, not whole-state equality. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer capCheckLeafCopyState checkLeafCopyState
  capCheckCompressionState checkCompressionState capCheckLeafTailPrefix checkLeafNextState

/-- Relocation changes the latch PC, while the reply and memory updates agree. -/
theorem cap_check_leaf_block_reference_memory (state : MachineState)
    (answer : BitVec 256) (scratch : state.getReg .x21 = 256) :
    (capCheckLeafBlockState state answer).mem = (checkLeafStepState state answer).mem := by
  have copiedScratch : (capCheckLeafCopyState state).getReg .x21 = 256 :=
    (cap_check_leaf_copy_register state .x21 (by decide)).trans scratch
  have nextMemory (current : MachineState) :
      (checkLeafNextState current).mem = current.mem := by
    unfold checkLeafNextState
    rfl
  have actual := cap_check_leaf_tail_memory
    (capCheckCompressionState (capCheckLeafCopyState state) answer)
  have compression := congrArg MachineState.mem
    (cap_check_compression_reference (capCheckLeafCopyState state) answer copiedScratch)
  have copied := congrArg (fun current => (checkCompressionState current answer).mem)
    (cap_check_leaf_copy_reference state)
  unfold capCheckLeafBlockState checkLeafStepState
  exact actual.trans (compression.trans (copied.trans (nextMemory _).symm))

end CommitGolfCandidate
