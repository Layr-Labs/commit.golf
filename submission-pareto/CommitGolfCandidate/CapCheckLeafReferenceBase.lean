import CommitGolfCandidate.CapCheckCompression
import CommitGolfCandidate.LeafRefinement

/-! The shared scratch compression block has the same data effect as the
published reference block. The stage-3 leaf no longer uses it; the lower path
still does. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer
attribute [local irreducible] List.foldl writeBits capCheckCompressionPrefix

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
