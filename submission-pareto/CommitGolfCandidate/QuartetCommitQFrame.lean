import CommitGolfCandidate.Execution
import CommitGolfCandidate.QuartetCommitRanges
import CommitGolfCandidate.QuartetManifest
import CommitGolfCandidate.TwoPermutationCommitSetup
import CommitGolfCandidate.TwoPermutationCounted
import CommitGolfCandidate.TwoPermutationManifest
import CommitGolfCandidate.TwoPermutationHeapInvariant
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] checkEvaluation packBuffer

def quadReply (oracle : Oracle) (children : Nat → Words 4) (g : Nat) :=
  oracle.permutation (packBuffer (quadWords children g))

structure QuadPrefix (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState) (count : Nat) : Prop where
  upper : ∀ i<count, (window (memoryView s) (qUpper i) : Words 4) = lowDigest (replyWords (quadReply oracle children i))
  high : ∀ w, qSource 0≤w → w<2^33 → memoryView s w=before w

theorem prefix_padded (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState) (g : Nat)
    (inv : QuadPrefix oracle before children s g) (ready : PaddedLeaves before children) : PaddedLeaves (memoryView s) children := by
  constructor
  · intro j hj k hk; rw [inv.high _ (by unfold qSource;omega) (by unfold qSource;omega)];exact ready.1 j hj k hk
  · intro i hi;apply Eq.trans _ (ready.2 i hi);funext k
    exact inv.high _ (by unfold qLeaf qSource;omega) (by unfold qLeaf qSource;have := k.isLt;omega)

end TwoPermutationPrototype.QuartetCommit
