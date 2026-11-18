import CommitGolfCandidate.QuartetCommitQLoop
import CommitGolfCandidate.TwoPermutationHeapInvariant
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] checkEvaluation qAfter packBuffer

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

theorem quad_prefix_step (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState) (g : Nat)
    (hg : g<4194304) (ready : PaddedLeaves before children) (inv : QuadPrefix oracle before children s g) :
    QuadPrefix oracle before children (qAfter s g (oracle.permutation (quadArgument s g))) (g+1) := by
  have input : quadArgument s g=packBuffer (quadWords children g) :=
    congrArg packBuffer (quad_input_words (memoryView s) children g hg (prefix_padded _ _ _ _ _ inv ready))
  rw [input]
  let raw := quadReply oracle children g
  change QuadPrefix oracle before children (qAfter s g raw) (g+1)
  obtain ⟨digest,prior,frame⟩ := upper_spill_frame (memoryView s) g hg raw
  have same := q_unit_memory s g raw hg
  constructor
  · intro i hi
    by_cases last : i=g
    · subst i;funext k
      exact (same _ (by unfold qUpper;have := k.isLt;omega)).trans (congrFun digest k)
    · apply Eq.trans _ (inv.upper i (by omega));funext k
      exact (same _ (by unfold qUpper;have := k.isLt;omega)).trans (prior i (by omega) k.val k.isLt)
  · intro w lo hi;exact (same w hi).trans ((frame w lo).trans (inv.high w lo hi))

end TwoPermutationPrototype.QuartetCommit
