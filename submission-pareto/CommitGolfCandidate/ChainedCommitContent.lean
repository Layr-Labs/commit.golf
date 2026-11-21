import CommitGolfCandidate.ChainedLeafContent

/-! Actual leaf initialization, all parent levels, and copied-root semantics. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open TwoPermutationPrototype TwoPermutationPrototype.Sampling
attribute [local irreducible] checkEvaluation readBuffer

theorem evaluation_read_bind (oracle : Oracle) (program : OracleComp World MachineState)
    (next : MachineState → OracleComp World MachineState) (address count : Nat) :
    readBuffer (checkEvaluation oracle (program >>= next)).1 address count =
      readBuffer (checkEvaluation oracle (next (checkEvaluation oracle program).1)).1 address count := by
  rw [check_evaluation_bind]

theorem chained_commit_body_root (oracle : Oracle) (ready : MachineState) (regs : Chain.BodyRegs ready)
    (salts : Index → BitVec 128)
    (original : ∀ i : Index, (window (memoryView ready) (leafSalt i.val) : Words 2) = saltWords (salts i)) :
    readBuffer (checkEvaluation oracle (chainedCommitBody ready)).1 4294971392 32 =
      (referenceHeap oracle (pinnedLeafNodes oracle ready) 1).setWidth 256 := by
  let middle := (checkEvaluation oracle (leafPrefixTrace ready)).1
  have reached := check_evaluation_support oracle (leafPrefixTrace ready)
  have content := (leaf_prefix_content oracle ready regs salts original).1
  have entry := leaf_prefix_heap_ready ready regs middle reached
  have output := leaf_prefix_output ready regs middle reached
  rw [chainedCommitBody,evaluation_read_bind]
  exact complete_parent_content oracle _ (reference_heap_tree oracle _) middle entry output content

end CommitGolfCandidate.Chained.Native
