import CommitGolfCandidate.R1bParentNodeContent
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation parentsTrace packedParentsTrace packedParentGroups hybridLowerFor hybridUpper hybridParentPhase readBuffer R1bParents.trace

theorem new_trace_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (n : Nat) (bound : n≤hybridCut)
    (tree : ∀ (i : Nat), 0 < i → i ≤ hybridCut → heap i=R1bParents.retained i (oracle.compression (heap (2*i+1) ++ heap (2*i))))
    (prior : ParentContent s heap salts n) (r : R1bParents.Ready s n) :
    ParentContent (checkEvaluation oracle (R1bParents.trace n s)).1 heap salts 0 := by
  induction n generalizing s with
  | zero => simpa only [R1bParents.trace,check_evaluation_pure] using prior
  | succ n ih =>
    rw [R1bParents.trace,check_evaluation_bind]
    have query : checkEvaluation oracle (liftM (World.query (.inr (.inl (parentInput s (n+1))))) :
        OracleComp World (BitVec 256))=(oracle.compression (parentInput s (n+1)),1) := CommitGolfCandidate.check_evaluation_public oracle _
    rw [query]
    let answer:=oracle.compression (parentInput s (n+1))
    have child : ParentContent (R1bParents.nextState s (n+1) answer) heap salts n :=
      new_node_content oracle s heap salts n (by change n+1<16777216;change n+1≤8388607 at bound;omega)
        (tree (n+1) (by omega) bound) prior r
    exact ih (R1bParents.nextState s (n+1) answer) (by omega) child (R1bParents.next_regs answer r)

end TwoPermutationPrototype.RV64
