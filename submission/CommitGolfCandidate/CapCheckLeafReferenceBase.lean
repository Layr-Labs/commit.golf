import CommitGolfCandidate.CapCheckLeafSubroutine
import CommitGolfCandidate.LeafRefinement

/-! Reusable semantics of the published salted leaf remain a separate reference.
The cap image executes newly fetched instructions at different PCs. These
identities reuse only the copy and scratch-write definitions, not old-image
execution or timing claims. Source separation is still required by the digest
copy refinement before applying the logical chain theorem. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer
attribute [local irreducible] List.foldl writeBits capCheckCompressionPrefix

theorem cap_check_leaf_copy_reference (state : MachineState) :
    capCheckLeafCopyState state = checkLeafCopyState state := by
  unfold capCheckLeafCopyState capWordCopyPrefix checkLeafCopyState
  apply congrArg (fun instructions : List Instr => instructions.foldl execInstrBr state)
  rfl

theorem cap_check_compression_reference (state : MachineState) (answer : BitVec 256)
    (scratch : state.getReg .x21 = 256) :
    capCheckCompressionState state answer = checkCompressionState state answer := by
  have pointer := (cap_check_compression_ready state scratch).2.2.2.1
  unfold capCheckCompressionState capCompressionAnswer
  rw [pointer]
  unfold checkCompressionState
  congr 1
  unfold capCheckCompressionPrefix
  apply congrArg (fun instructions : List Instr => instructions.foldl execInstrBr state)
  rfl

end CommitGolfCandidate
