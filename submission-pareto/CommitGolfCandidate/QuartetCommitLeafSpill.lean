import CommitGolfCandidate.QuartetCommitLeafOps
import CommitGolfCandidate.QuartetManifest
import CommitGolfCandidate.TwoPermutationManifest
import CommitGolfCandidate.TwoPermutationPinnedCommitSpec
import CommitGolfCandidate.TwoPermutationCounted
namespace TwoPermutationPrototype.RV64.QuartetLeaves
open TwoPermutationPrototype.QuartetCommit
open TwoPermutationPrototype.RV64.PackedLeaves (pinnedWords rawPrefix pinnedWrites stamp pinned_digest_words pinned_word_outside)
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
def pinnedFinalReply (oracle : Oracle) (mem : Memory) (i : Nat) : BitVec 1600 :=
  let msg := window mem (leafStart i+5)
  let salt := window mem (qSalt i)
  let a := oracle.permutation (packBuffer (rawPrefix msg))
  oracle.permutation (packBuffer (pinnedWords (secondTag i) salt (replyWords a) msg))

structure PinnedLeafPrefix (oracle : Oracle) (before : Memory) (s : MachineState) (count : Nat) : Prop where
  digests : ∀ i < count, (window (memoryView s) (qLeaf i) : Words 4) =
    lowDigest (replyWords (pinnedFinalReply oracle before i))
  messages : ∀ i, count ≤ i → i < 2^24 → (window (memoryView s) (leafStart i+5) : Words 32) =
    window before (leafStart i+5)
  salts : ∀ i < 2^24, (window (memoryView s) (qSalt i) : Words 2) = window before (qSalt i)

  padding : ∀ g<4194304, ∀ k<9, memoryView s (qSource g+k)=0

theorem empty_prefix (oracle : Oracle) (s : MachineState) (pad : ∀ g<4194304, ∀ k<9, memoryView s (qSource g+k)=0) :
    PinnedLeafPrefix oracle (memoryView s) s 0 := ⟨fun _ h => False.elim (by omega),fun _ _ _ => rfl,fun _ _ => rfl,pad⟩


end TwoPermutationPrototype.RV64.QuartetLeaves
